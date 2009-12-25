#
#

from variable import *
from expression import SimpleRef
from pprint import pformat


class Stmt(object):
    """Statement object
    """

    def __init__(self):
        self._labels = []
        self.ip = None
    
    def __repr__(self):
        return "STMT@%d[%s]: %s" % (self.ip, self.executable(), self.execute())

    def executable(self):
        """Generates C code which evaluates to 1 if statement is executable
        """
        return "1"

    def execute(self):
        """Generates C code which executes statement

        Needs not to end with semicolon
        """
        return ""

    def add_label(self, label):
        """Adds label to statement
        
        Arguments:
        - `label`: Label object
        """
        self._labels.append(label)
        label.parent = self


class AssignStmt(Stmt):
    """Assignment statement

    Always executable
    """
    
    def __init__(self, varref, expr):
        """
        
        Arguments:
        - `varref`: VarRef object to assign to
        - `expr`: Expression object
        """
        Stmt.__init__(self)
        self._varref = varref
        self._expr = expr

    def execute(self):
        return "%s = %s" % (self._varref.code(), self._expr.code())


class IncDecStmt(Stmt):
    """Increment/decrement statement

    Always executable
    """
    
    def __init__(self, varref, op):
        """
        
        Arguments:
        - `varref`: VarRef object to increment/decrement
        - `op`: operator ('++' or '--')
        """
        Stmt.__init__(self)
        self._varref = varref
        self._op = op

    def execute(self):
        return "%s%s" % (self._op, self._varref.code())


class GotoStmt(Stmt):
    """Goto statement
    """
    
    def __init__(self, label):
        """
        
        Arguments:
        - `label`: Label object
        """
        Stmt.__init__(self)
        self._label = label

    def execute(self):
        return "IP = %s" % str(self._label.ip)


class ExprStmt(Stmt):
    """Expression statement

    Executable, when expression is != 0.
    Does nothing
    """
    
    def __init__(self, expr):
        """
        
        Arguments:
        - `expr`: Expression object
        """
        Stmt.__init__(self)
        self._expr = expr

    def execute(self):
        return ""

    def executable(self):
        return self._expr.code()


class ElseStmt(ExprStmt):
    """Else statement

    This is actually an expression that is 1 when all other branches
    are non-executable
    """

    else_var = Variable("ELSE", Type('bool'))
    
    def __init__(self):
        ExprStmt.__init__(self, SimpleRef(self.else_var))
        

class BreakStmt(Stmt):
    """Break statement

    Always executable
    """
    
    def execute(self):
        return "BREAK";


class AssertStmt(Stmt):
    """Assertion statement

    Always executable
    """
    
    def __init__(self, expr):
        """
        
        Arguments:
        - `expr`: Expr object whose value is asserted to be != 0
        """
        Stmt.__init__(self)
        self._expr = expr

    def execute(self):
        return "ASSERT(%s)" % self._expr.code()


class IfStmt(Stmt):
    """If statement

    In current naive implementation, it's always executable and acts like no-op.
    It's main purpose is generating multiple transition branches
    """
    
    def __init__(self, options):
        """
        
        Arguments:
        - `options`: list of lists of Stmt objects; each list is a branch
        """
        Stmt.__init__(self)
        self._options = options

    def __repr__(self):
        return "IF: %s" % pformat(self._options)


class DoStmt(IfStmt):
    """Do statement

    Acts similar to IfStmt
    """
    
    def __init__(self, options):
        """
        
        Arguments:
        - `options`: list of lists of Stmt objects; each list is a branch
        """
        IfStmt.__init__(self, options)

    def __repr__(self):
        return "DO: %s" % pformat(self._options)
