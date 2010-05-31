#!/usr/bin/env python

from expression import *
from statement import *
from variable import *
from unittest import TestCase, main


class ExprExecTestCase(TestCase):
    def setUp(self):
        c2 = ConstExpr(2)
        vx = Variable("x", SimpleType('int'))
        vy = Variable("y", SimpleType('int'))
        vch = Channel("ch", 10, [SimpleType('int')])
        rx = SimpleRef(vx)
        ry = SimpleRef(vy)
        uexp1 = BinaryExpr(rx, '>', ry)
        self.noop = NoopStmt("NOP")
        self.expr = ExprStmt(uexp1)
        self.inc = IncDecStmt(ry, '--')
        self.asrt = AssertStmt(uexp1)
        self.asgn = AssignStmt(rx, c2)
        self.atmc1 = AtomicStmt([self.expr, self.noop])
        self.else1 = ElseStmt()
        self.if1 = IfStmt([[self.expr, self.inc],
                           [self.else1]])
        self.do1 = DoStmt([[self.expr, self.inc],
                           [self.noop]])

    def test_simple(self):
        def T(stmt, code1, code2):
            self.assertEqual(stmt.executable(), code1)
            self.assertEqual(stmt.execute(), code2)
        T(self.noop, "1", "")
        T(self.expr, "((x) > (y))", "")
        T(self.inc, "1", "--(y)")

    def test_complex(self):
        def T(stmt, code1, code2):
            self.assertEqual(stmt.executable(), code1)
            self.assertEqual(stmt.execute(), code2)
        T(self.asrt, "1", 'ASSERT(((x) > (y)), "(x > y)")')
        T(self.asgn, "1", "(x) = 2")
        T(self.atmc1, "((x) > (y))", "BEGIN_ATOMIC()")

    def test_cond(self):
        def T(stmt, code1, code2):
            self.assertEqual(stmt.executable(), code1)
            self.assertEqual(stmt.execute(), code2)
        T(self.else1, "(!(((x) > (y))))", "")
        T(self.if1, "1", "")
        T(self.do1, "(((x) > (y)) || 1)", "")


if __name__ == '__main__':
    main()
