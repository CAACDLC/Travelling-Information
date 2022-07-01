# The MIT License (MIT)
# Copyright (c) 2016 Arie Gurfinkel

# Permission is hereby granted, free of charge, to any person obtaining
# a copy of this software and associated documentation files (the
# "Software"), to deal in the Software without restriction, including
# without limitation the rights to use, copy, modify, merge, publish,
# distribute, sublicense, and/or sell copies of the Software, and to
# permit persons to whom the Software is furnished to do so, subject to
# the following conditions:

# The above copyright notice and this permission notice shall be
# included in all copies or substantial portions of the Software.

# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
# EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
# LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
# OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
# WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

import sys

import io 
import z3

from . import ast, int


class SymState(object):
    def __init__(self, solver=None):
        # environment mapping variables to symbolic constants
        self.env = dict()
        # path condition
        self.path = list()
        self._solver = solver
        if self._solver is None:
            self._solver = z3.Solver()

        # true if this is an error state
        self._is_error = False

    def add_pc(self, *exp):
        """Add constraints to the path condition"""
        self.path.extend(exp)
        self._solver.append(exp)

    def is_error(self):
        return self._is_error

    def mk_error(self):
        self._is_error = True

    def is_empty(self):
        """Check whether the current symbolic state has any concrete states"""
        res = self._solver.check()
        return res == z3.unsat

    def pick_concerete(self):
        """Pick a concrete state consistent with the symbolic state.
           Return None if no such state exists"""
        res = self._solver.check()
        if res != z3.sat:  #### 未做修改
            return None
        model = self._solver.model()
        st = int.State()
        for (k, v) in self.env.items():
            st.env[k] = model.eval(v)
        return st

    def fork(self):
        """Fork the current state into two identical states that can evolve separately"""
        child = SymState()
        child.env = dict(self.env)
        child.add_pc(*self.path)

        return (self, child)

    def __repr__(self):
        return str(self)

    def to_smt2(self):
        """Returns the current state as an SMT-LIB2 benchmark"""
        return self._solver.to_smt2()

    def __str__(self):
        buf = io.StringIO()
        for k, v in self.env.items():
            buf.write(str(k))
            buf.write(': ')
            buf.write(str(v))
            buf.write('\n')
        buf.write('pc: ')
        buf.write(str(self.path))
        buf.write('\n')

        return buf.getvalue()


class SymExec(ast.AstVisitor):
    def __init__(self):
        pass

    def run(self, ast, state):
        # set things up and
        # call self.visit (ast, state=state)
        return self.visit(ast, state = state)
       

    def visit_IntVar(self, node, *args, **kwargs):
        return kwargs['state'].env[node.name]

    def visit_BoolConst(self, node, *args, **kwargs):
        return z3.BoolVal(node.val)

    def visit_IntConst(self, node, *args, **kwargs):
        return z3.IntVal(node.val)

    def visit_RelExp(self, node, *args, **kwargs):
        lhs = self.visit(node.arg(0), *args, **kwargs)
        rhs = self.visit(node.arg(1), *args, **kwargs)
        if node.op == "<=":
            return lhs <= rhs
        if node.op == "<":
            return lhs < rhs
        if node.op == "=":
            return lhs == rhs
        if node.op == ">=":
            return lhs >= rhs
        if node.op == ">":
            return lhs > rhs

        assert False
        

    def visit_BExp(self, node, *args, **kwargs): 
        kids = [self.visit(a, *args, **kwargs) for a in node.args]
        if node.op == 'not':
            assert node.is_unary()
            assert len(kids) == 1
            return z3.Not(kids[0])
            fn = None
            base = None
        if node.op == 'and':
            fn = lambda x, y :z3.And(x,y)
            base = z3.BoolVal(True)
        elif node.op == 'or':
            fn = lambda x, y : z3.Or(x,y)
            base = z3.BoolVal(False)

        assert fn is not None
        return reduce (fn, kids, base)

    def visit_AExp(self, node, *args, **kwargs):
        kids = [self.visit(a, *args, **kwargs) for a in node.args]

        fn = None

        if node.op == '+':
            fn = lambda x, y: x + y
        elif node.op == '-':
            fn = lambda x, y: x - y
        elif node.op == '*':
            fn = lambda x, y: x * y
        elif node.op == '/':
            fn = lambda x, y: x / y

        assert fn is not None
        return reduce(fn, kids)
       

    def visit_SkipStmt(self, node, *args, **kwargs): #需要解释
        return [kwargs['state']]

    def visit_PrintStateStmt(self, node, *args, **kwargs):
      
        print(kwargs['state'])
        return [kwargs['state']]

    def visit_AsgnStmt(self, node, *args, **kwargs):
        exp = self.visit(node.rhs, *args, **kwargs)
        state = kwargs['state']
        state.env[node.lhs.name] = z3.FreshInt(node.lhs.name)
        state.add_pc(state.env[node.lhs.name] == exp)
        return [state]
       

    def visit_IfStmt(self, node, *args, **kwargs):
        cond = self.visit(node.cond, *args, **kwargs)
        states = []
        if_states = kwargs['state'].fork()
        cond_state = if_states[0]
        not_cond_state = if_states[1]
        
        if cond_state.addcond_isSolvable(cond):
            states.extend(self.visit(node.then_stmt, state=cond_state))

        if not_cond_state.addcond_isSolvable(z3.Not(cond)):
            if node.has_else():
                states.extend(self.visit(node.else_stmt, state=not_cond_state))
            else:
                states.append(not_cond_state)
        return states    

    def visit_WhileStmt(self, node, *args, **kwargs):
        pass
        

    def visit_AssertStmt(self, node, *args, **kwargs):
        # Don't forget to print an error message if an assertion might be violated
        cond = self.visit(node.cond, *args, **kwargs)
        states = kwargs['state'].fork()
        cond_states = states[0]
        not_cond_states = states[1]
        # if cond cannot be satisfied, print an error message
        if not_cond_states.addcond_isSolvable(z3.Not(cond)):
            print("Assertion error")
            not_cond_states.mk_error()
        
        if  cond_states.addcond_isSolvable(cond):
            return [cond_states]
        else:
            return []
        

    def visit_AssumeStmt(self, node, *args, **kwargs):
        st = kwargs['state']
        st.add_pc(self.visit(node.cond, *args, **kwargs))
        return [st] if not st.is_empty() else []

    def visit_HavocStmt(self, node, *args, **kwargs):
        state = kwargs['state']
        for var in node.vars:
            state.env[var.name] = z3.FreshInt(var.name)
        return [state]

    def visit_StmtList(self, node, *args, **kwargs):
       
        states = [kwargs['state']]
        # for each statement in stmts, update the state list
        for stmt in node.stmts:
            updates_states = []
            for state in states:
                updates_states.extend(self.visit(stmt, state=state))
            states = updates_states
        return states


def _parse_args():
    import argparse
    ap = argparse.ArgumentParser(prog='sym',
                                 description='WLang Interpreter')
    ap.add_argument('in_file', metavar='FILE',
                    help='WLang program to interpret')
    args = ap.parse_args()
    return args


def main():
    args = _parse_args()
    prg = ast.parse_file(args.in_file)
    st = SymState()
    sym = SymExec()

    states = sym.run(prg, st)
    if states is None:
        print('[symexec]: no output states')
    else:
        count = 0
        for out in states:
            count = count + 1
            print('[symexec]: symbolic state reached')
            print(out)
        print('[symexec]: found', count, 'symbolic states')
    return 0


if __name__ == '__main__':
    sys.exit(main())
