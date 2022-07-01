r'''
Date: 2022-06-09 14:18:30
LastEditors: Zihang Zhou
LastEditTime: 2022-07-01 16:15:57
FilePath: \a2\wlang\test_sym.py
'''
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

import unittest

from . import ast, sym


class TestSym (unittest.TestCase):
    def test_one(self):
        prg1 = "a := 1; b := 1; c := a + b;"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 1)
   
    # def test_aha (self):
    #     prg1 = """{a := 1;
    #         b := -1;
    #         c := a + b; d := b - a;
    #         e := a * b; f := a / b};
    #         if a > 1 and a >= b then b := 3; 
    #         if a <= 1 or b < 3 then a := 1; 
    #         if false and not a = 1 then a := 1 else print_state; 
    #         skip;
    #         print_state;
    #         while (a < 3) or (b = 1) and true do {a := a + 1};
    #         assume b = -1;
    #         havoc c,d;
    #         assert a = 3;
    #         assert a = 2"""

    #     ast1 = ast.parse_string (prg1)
    #     sym = wlang.sym.SymExec ()
    #     st = wlang.sym.SymState ()
    #     st.pick_concerete()
    #     st.is_error()
    #     st.mk_error()
    #     st.to_smt2()
    #     repr(st)
    #     out = [s for s in sym.run (ast1, st)]
    #     # self.assertEquals (len(out), 1)

    #     st2 = wlang.sym.SymState() 
    #     st2.add_pc(z3.BoolVal(True) )
    #     st2.add_pc(z3.BoolVal(False) )
    #     st2.pick_concerete()
