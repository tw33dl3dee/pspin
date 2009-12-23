#
#

class Expr(object):
    def __repr__(self):
        return self.code()


class ConstExpr(Expr):
    """Constant expression
    """
    
    def __init__(self, value):
        """
        
        Arguments:
        - `value`: Expression value (int)
        """
        Expr.__init__(self)
        self._value = value

    def code(self):
        return str(self._value)


class VarRef(Expr):
    """Reference to a variable
    """
    pass


class SimpleRef(VarRef):
    """Direct reference to a variable
    """
    
    def __init__(self, var):
        """
        
        Arguments:
        - `var`: Variable object
        """
        Expr.__init__(self)
        self._var = var

    def code(self):
        return self._var.ref()


class IdxRef(VarRef):
    """Indexed reference to a variable
    """
    
    def __init__(self, var, idx):
        """
        
        Arguments:
        - `var`: Variable object
        - `idx`: Index (int)
        """
        Expr.__init__(self)
        self._var = var
        self._idx = idx

    def code(self):
        return "(%s[%s])" % (self._var.ref(), self._idx)


class FieldRef(VarRef):
    """Reference to a field of another variable reference
    """
    
    def __init__(self, varref, field):
        """
        
        Arguments:
        - `varname`: VarRef object
        - `field`:Field name
        """
        Expr.__init__(self)
        self._varref = varref
        self._field = field
        
    def ref(self):
        return "(%s.%s)" % (self._varref.code(), self._idx)


class RunExpr(Expr):
    """Run process
    """
    
    def __init__(self, proctype, args, prio):
        """
        
        Arguments:
        - `proctype`: Process name
        - `args`: Arguments (list of Expr objects)
        - `prio`: Priority (int)
        """
        Expr.__init__(self)
        self._proctype = proctype
        self._args = args
        self._prio = prio

    def code(self):
        """
        """
        return NotImplemented


class TernaryExpr(Expr):
    """Ternary expression (the only instance of which in PROMELA is ?:)
    """
    
    def __init__(self, left, op1, mid, op2, right):
        """
        
        Arguments:
        - `left`: Left Expr object
        - `op1`: First part of op (str)
        - `mid`: Mid Expr object
        - `op2`: Second part of op (str)
        - `right`: Right Expr object
        """
        Expr.__init__(self)
        self._left = left
        self._op1 = op1
        self._mid = mid
        self._op2 = op2
        self._right = right

    def code(self):
        """
        """
        return "(%s %s %s %s %s)" % (self._left.code(), self._op1, self._mid.code(), self._op2, self._right.code())


class BinaryExpr(Expr):
    """Binary expression
    """
    
    def __init__(self, left, op, right):
        """
        
        Arguments:
        - `left`: Left Expr object
        - `op`: Operator (str)
        - `right`: Right Expr object
        """
        Expr.__init__(self)
        self._left = left
        self._op = op
        self._right = right

    def code(self):
        return "(%s %s %s)" % (self._left.code(), self._op, self._right.code())


class UnaryExpr(Expr):
    """Unary expression
    """
    
    def __init__(self, op, right):
        """
        
        Arguments:
        - `op`: Unary operator
        - `right`: Operand Expr object
        """
        Expr.__init__(self)
        self._op = op
        self._right = right

    def code(self):
        return "(%s %s)" % (self._op, self._right.code())


class ChanOpExpr(Expr):
    """Channel operation (len, full, etc)
    """
    
    def __init__(self, op, chan):
        """
        
        Arguments:
        - `op`: Operator name (str)
        - `chan`: Channel (VarRef object)
        """
        Expr.__init__(self)
        self._op = op
        self._chan = chan
    
    def code(self):
        """
        """
        return "chan_%s(%s)" % (self._op, self._chan.code())
