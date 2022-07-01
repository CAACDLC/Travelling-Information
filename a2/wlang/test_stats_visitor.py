r'''
Date: 2022-06-09 14:18:30
LastEditors: Zihang Zhou
LastEditTime: 2022-07-01 13:30:36
FilePath: \a2\wlang\test_stats_visitor.py
'''
import unittest

from . import ast, stats_visitor


class TestStatsVisitor (unittest.TestCase):
    pass
    
    def test_one(self):
        prg1 = "x := 10; print_state"
        ast1 = ast.parse_string(prg1)

        sv = stats_visitor.StatsVisitor()
        sv.visit(ast1)
        # UNCOMMENT to run the test
        self.assertEquals(sv.get_num_stmts(), 2)
        self.assertEquals(sv.get_num_vars(), 1)
    