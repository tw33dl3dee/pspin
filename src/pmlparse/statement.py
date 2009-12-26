#
#

from variable import *
from expression import SimpleRef
from pprint import pformat
from utils import flatten


class Stmt(object):
    """Statement object
    """

    def __init__(self):
        self._labels = []
        self.ip = None
        self._next = []
        self._prev = None
    
    def __repr__(self):
        return "STMT(@%s -> %s)[%s]: %s" % (self.ip, [s.ip for s in self._next], self.executable(), self.execute())

    def executable(self):
        """Generates C expression which evaluates to 1 if statement is executable
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

    def set_next(self, stmt):
        """Sets next statement for current statement
        
        Arguments:
        - `stmt`: Stmt object
        """
        self._next = [stmt]

    @property
    def next(self):
        """List of next statements (reachable immeaditaly after current is executed)

        All statements in list are atomic statements (no if/do blocks)
        """
        return self._next

    @property
    def prev(self):
        """Prev statement (from which this statement is reachable)

        Could be a compound statement (if/do)
        """
        return self._prev

    def set_prev(self, stmt):
        """Sets next statement for current statement

        Is used in if/do to fixup links of preceding statements
        """
        self._prev = stmt

    def find_break_stmts(self):
        """Finds all BreakStmt instances in current scope (statement and sub-statements)

        For most statements, does nothing. TO be overloaded in block statements.
        Returns (possibly deep) list of BreakStmt objects
        """
        return []


class CompoundStmt(Stmt, list):
    """Compound statement.

    This statement is never used on it's own, only for if/do statements
    for transition generation and executability checks.
    Is executable if first statement is executable
    """
    
    def __init__(self, stmts):
        """
        
        Arguments:
        - `stmts`: list of Stmt objects
        """
        Stmt.__init__(self)
        list.__init__(stmts)

    def executable(self):
        # Empty block is always executable
        return len(self) and self[0].executable() or "1"

    def execute(self):
        raise NotImplementedError


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


class ElseStmt(Stmt):
    """Else statement

    This is an expression that is 1 when all other branches are non-executable
    Actual expression (`cond`) is set by parent if/do statement
    """
    
    def __init__(self):
        Stmt.__init__(self)
        self.cond = None

    def executable(self):
        if self.cond is None:
            raise RuntimeError, "`else' not in guard"
        return self.cond


class BreakStmt(Stmt):
    """Break statement

    Always executable, does nothing
    """

    def find_break_stmts(self):
        return [self]


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

    Executable when at least one of it's branches is executable.
    Executes as no-op.
    It's main purpose is generating multiple transition branches
    """
    
    def __init__(self, options):
        """
        
        Arguments:
        - `options`: list of lists of Stmt objects; each list is a branch
        """
        Stmt.__init__(self)
        self._options = options
        self._next = [branch[0] for branch in options]
        self._has_else = False
        for branch in options:
            if type(branch[0]) is ElseStmt:
                if self._has_else:
                    raise RuntimeError, "Multiple `else' branches"
                # This MUST be called before `has_else` is set to True, otherwise `cond` will always be "!1"
                branch[0].cond = "(!%s)" % (self.executable())
                self._has_else = True

    def __repr__(self):
        return "(@%s -> %s)[%s]: IF: %s" % (self.ip, [s.ip for s in self._next], self.executable(), pformat(self._options))

    def set_next(self, stmt):
        for branch in self._options:
            branch[-1].set_next(stmt)

    def set_prev(self, stmt):
        self._prev = self._options[0][0].prev
        self._prev.set_next(self)
        stmt.set_next(self)

    def find_break_stmts(self):
        return [s.find_break_stmts() for branch in self._options for s in branch]

    def executable(self):
        if self._has_else:
            # if/do having `else' branch is always executable
            return "1"
        # We still need to filter out ElseStmt as we are called before `has_else` is set to True
        # to generate ElseStmt condition code
        return "(%s)" % " || ".join([branch[0].executable() for branch in self._options if type(branch[0]) is not ElseStmt])


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

    def set_next(self, stmt):
        super(DoStmt, self).set_next(self)
        brk_stmts = flatten([s.find_break_stmts() for branch in self._options for s in branch])
        for brk in brk_stmts:
            brk.set_next(stmt)

    def find_break_stmts(self):
        # `break' should not be sought in inner do-blocks
        return []

    def __repr__(self):
        return "(@%s -> %s)[%s]: DO:\n%s" % (self.ip, [s.ip for s in self._next], self.executable(), pformat(self._options))
