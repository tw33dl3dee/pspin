#
#

class Expr(object):
    def __str__(self):
        """Returns human-readable expression representation
        """
        return self.code()

    def code(self):
        """Returns C expression which evaluates current expression value
        """
        raise NotImplementedError


class ConstExpr(Expr):
    """Constant expression
    """

    def __init__(self, value):
        """

        Arguments:
        - `value`: expression value (int)
        """
        Expr.__init__(self)
        self._value = value

    def code(self):
        return str(self._value)


class VarRef(Expr):
    """Reference to a variable
    """
    def deref(self):
        """Returns Variable object being referenced
        """
        return NotImplemented


class SimpleRef(VarRef):
    """Direct reference to a variable
    """

    def __init__(self, var):
        """

        Arguments:
        - `var`: Variable object
        """
        VarRef.__init__(self)
        self._var = var

    def __str__(self):
        return str(self._var)

    def code(self):
        return self._var.ref()

    def deref(self):
        return self._var


class IdxRef(VarRef):
    """Indexed reference to a variable
    """

    def __init__(self, var, idx):
        """

        Arguments:
        - `var`: Variable object
        - `idx`: index (Expression object)
        """
        VarRef.__init__(self)
        self._var = var
        self._idx = idx

    def __str__(self):
        return "%s[%s]" % (self._var, self._idx)

    def code(self):
        return "(%s[%s])" % (self._var.ref(), self._idx.code())

    def deref(self):
        return self._var


class FieldRef(VarRef):
    """Reference to a field of another variable reference
    """

    def __init__(self, varref, field):
        """

        Arguments:
        - `varname`: VarRef object
        - `field`: field name
        """
        VarRef.__init__(self)
        self._varref = varref
        self._field = field

    def __str__(self):
        return "%s.%s" % (self._varref, self._field)

    def ref(self):
        return "(%s.%s)" % (self._varref.code(), self._field)


class RunExpr(Expr):
    """Run process
    """

    def __init__(self, proctype, args, prio):
        """

        Arguments:
        - `proctype`: process name
        - `args`: arguments (list of Expr objects)
        - `prio`: priority (int)
        """
        Expr.__init__(self)
        self._proctype = proctype
        self._args = args
        self._prio = prio

    def code(self):
        return NotImplemented


class TernaryExpr(Expr):
    """Ternary expression (the only instance of which in PROMELA is ?:)
    """

    def __init__(self, left, op1, mid, op2, right):
        """

        Arguments:
        - `left`: left Expr object
        - `op1`: first part of op (str)
        - `mid`: mid Expr object
        - `op2`: second part of op (str)
        - `right`: right Expr object
        """
        Expr.__init__(self)
        self._left = left
        self._op1 = op1
        self._mid = mid
        self._op2 = op2
        self._right = right

    def __str__(self):
        return "(%s %s %s %s %s)" % (self._left, self._op1, self._mid, self._op2, self._right)

    def code(self):
        return "(%s %s %s %s %s)" % (self._left.code(), self._op1, self._mid.code(), self._op2, self._right.code())


class BinaryExpr(Expr):
    """Binary expression
    """

    def __init__(self, left, op, right):
        """

        Arguments:
        - `left`: left Expr object
        - `op`: operator (str)
        - `right`: right Expr object
        """
        Expr.__init__(self)
        self._left = left
        self._op = op
        self._right = right

    def __str__(self):
        return "(%s %s %s)" % (self._left, self._op, self._right)

    def code(self):
        return "(%s %s %s)" % (self._left.code(), self._op, self._right.code())


class UnaryExpr(Expr):
    """Unary expression
    """

    def __init__(self, op, right):
        """

        Arguments:
        - `op`: unary operator
        - `right`: operand Expr object
        """
        Expr.__init__(self)
        self._op = op
        self._right = right

    def __str__(self):
        return "(%s%s)" % (self._op, self._right)

    def code(self):
        return "(%s%s)" % (self._op, self._right.code())


class ChanOpExpr(Expr):
    """Channel operation (len, full, etc)
    """

    def __init__(self, op, chan):
        """

        Arguments:
        - `op`: operator name (str)
        - `chan`: channel (VarRef object)
        """
        Expr.__init__(self)
        self._op = op.upper()
        self._chan = chan

    def __str__(self):
        return "CHAN_%s(%s)" % (self._op, self._chan)

    def code(self):
        return "CHAN_%s(%s)" % (self._op, self._chan.code())
