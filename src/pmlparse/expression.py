#
#

class Expr(object):
    def __repr__(self):
        return self.code()


class RunExpr(Expr):
    """
    """
    
    def __init__(self, proctype, args, prio):
        """
        
        Arguments:
        - `proctype`:
        - `args`:
        """
        self._proctype = proctype
        self._args = args
        self._prio = prio

    def code(self):
        """
        """
        return "<run (%s, %s, %s)>" % (self._proctype, self._args, self._prio)


class TernaryExpr(Expr):
    """
    """
    
    def __init__(self, left, op1, mid, op2, right):
        """
        
        Arguments:
        - `left`:
        - `op1`:
        - `mid`:
        - `op2`:
        - `right`:
        """
        self._left = left
        self._op1 = op1
        self._mid = mid
        self._op2 = op2
        self._right = right

    def code(self):
        """
        """
        return "(%s %s %s %s %s)" % (self._left, self._op1, self._mid, self._op2, self._right)


class BinaryExpr(Expr):
    """
    """
    
    def __init__(self, left, op, right):
        """
        
        Arguments:
        - `left`:
        - `op`:
        - `right`:
        """
        self._left = left
        self._op = op
        self._right = right

    def code(self):
        return "(%s %s %s)" % (self._left, self._op, self._right)


class UnaryExpr(Expr):
    """
    """
    
    def __init__(self, op, right):
        """
        
        Arguments:
        - `op`:
        - `right`:
        """
        self._op = op
        self._right = right

    def code(self):
        return "(%s %s)" % (self._op, self._right)


class FuncallExpr(object):
    def code(self):
        return "<funcall"


class ChanOpExpr(Expr):
    """
    """
    
    def __init__(self, op, chan):
        """
        
        Arguments:
        - `op`:
        - `chan`:
        """
        self._op = op
        self._chan = chan
    
    def code(self):
        """
        """
        return "chan_%s(%s)" % (self._op, self._chan)
