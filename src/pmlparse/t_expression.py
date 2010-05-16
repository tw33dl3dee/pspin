#!/usr/bin/env python
##

from expression import *
from variable import *
from unittest import TestCase, main


class ExprExecTestCase(TestCase):
    def setUp(self):
        self.cm1 = ConstExpr(-1)
        self.c0 = ConstExpr(0)
        self.c1 = ConstExpr(1)
        self.c2 = ConstExpr(2)
        self.vx = Variable("x", SimpleType('int'))
        self.vy = Variable("y", SimpleType('int'))
        self.vz = Variable("z", SimpleType('int'))
        self.vch = Channel("ch", 10, [SimpleType('int')])
        self.rx = SimpleRef(self.vx)
        self.ry = SimpleRef(self.vy)
        self.rz = SimpleRef(self.vz)
        self.rch = SimpleRef(self.vch)
        self.uexp1 = UnaryExpr('-', self.c0)
        self.uexp2 = UnaryExpr('+', self.rx)
        self.bexp1 = BinaryExpr(self.uexp1, '+', self.ry)
        self.bexp2 = BinaryExpr(self.bexp1, '*', self.c2)
        self.texp1 = TernaryExpr(self.uexp2, '?', self.bexp2, ':', self.c2)
        self.chexp = ChanOpExpr('len', self.rch)

    def test_simple(self):
        def T(expr, res, cres):
            self.assertEqual(expr.code(), res)
            self.assertEqual(expr.eval(), cres)
        T(self.cm1, "-1", -1)
        T(self.c0, "0", 0)
        T(self.c1, "1", 1)
        T(self.c2, "2", 2)

    def test_vars(self):
        def T(expr, res, cres):
            self.assertEqual(expr.code(), res)
            self.assertEqual(expr.eval(), cres)
        T(self.rx, "(x)", None)
        T(self.ry, "(y)", None)
        T(self.rz, "(z)", None)
        T(self.rch, "(ch)", None)

    def test_composite(self):
        def T(expr, res, cres):
            self.assertEqual(expr.code(), res)
            self.assertEqual(expr.eval(), cres)
        T(self.uexp1, "(-0)", 0)
        T(self.uexp2, "(+(x))", None)
        T(self.bexp1, "((-0) + (y))", None)
        T(self.bexp2, "(((-0) + (y)) * 2)", None)
        T(self.texp1, "((+(x)) ? (((-0) + (y)) * 2) : 2)", None)

    def test_chan(self):
        def T(expr, res):
            self.assertEqual(expr.code(), res)
        T(self.chexp, "CHAN_LEN((ch))")

if __name__ == '__main__':
    main()
