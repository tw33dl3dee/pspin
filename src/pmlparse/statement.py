#
#

from variable import *
from expression import SimpleRef, ChanOpExpr
from utils import flatten, enum
from string import Template


class Stmt(object):
    """Statement object
    """

    def __init__(self):
        self._labels = []
        self.ip = None
        self._next = []
        self._prev = None
        self._parent_proc = None
        self._starts_atomic = False
        self._ends_atomic = False
        self._starts_dstep = False
        self._ends_dstep = False
        self._omittable = False
        self._endstate = False

    def __str__(self):
        return self.debug_repr()

    def debug_repr(self):
        """Returns human-readable representation of statement
        """
        return self.execute()

    def executable(self):
        """Generates C expression which evaluates to 1 if statement is executable
        """
        return "1"

    def execute(self):
        """Generates C code which executes statement

        Needs not to end with semicolon
        """
        return ""

    def pre_exec(self):
        """Generates C code to execute before the statement

        Needs not to end with semicolon
        """
        lines = []
        if self.starts_dstep and not self.ends_dstep:
            lines.append("BEGIN_DSTEP()")
        if self.starts_atomic and not self.ends_atomic:
            lines.append("BEGIN_ATOMIC()")
        return len(lines) and "; ".join(lines) or None

    def post_exec(self):
        """Generates C code to execute after the statement

        Needs not to end with semicolon
        """
        lines = []
        if not self.starts_atomic and self.ends_atomic:
            lines.append("END_ATOMIC()")
        if not self.starts_dstep and self.ends_dstep:
            lines.append("END_DSTEP()")
        return len(lines) and "; ".join(lines) or None

    def set_atomic(self, starts, ends):
        """Sets atomicity context of statement

        Arguments:
        - `starts`: if True, starts atomic context
        - `ends`: if True, ends atomic context

        If any argument is None, corresponding flag is left unchanged
        """
        if starts is not None:
            self._starts_atomic = starts
        if ends is not None:
            self._ends_atomic = ends

    def set_dstep(self, starts, ends):
        """Sets d_step context of statement

        Arguments:
        - `starts`: if True, starts d_step context
        - `ends`: if True, ends d_step context

        If any argument is None, corresponding flag is left unchanged
        """
        if starts is not None:
            self._starts_dstep = starts
        if ends is not None:
            self._ends_dstep = ends

    @property
    def starts_atomic(self):
        return self._starts_atomic

    @property
    def ends_atomic(self):
        return self._ends_atomic

    @property
    def starts_dstep(self):
        return self._starts_dstep

    @property
    def ends_dstep(self):
        return self._ends_dstep

    @property
    def omittable(self):
        """If True, statement may be left out (by graph reduction) with no side effect
        """
        return self._omittable

    @property
    def endstate(self):
        """If True, this statement is considered a valid endstate
        """
        return self._endstate

    def set_endstate(self, endstate):
        """Sets statement endstate flag to given value, if not None
        """
        if endstate:
            self._endstate = endstate

    def add_label(self, label):
        """Adds label to statement

        Arguments:
        - `label`: Label object
        """
        self._labels.append(label)
        label.parent_stmt = self

    def set_next(self, stmt):
        """Sets next statement for current statement
        
        MUST be called before complementary set_prev

        Arguments:
        - `stmt`: Stmt object
        """
        self._next = [stmt]

    @property
    def next(self):
        """List of next statements (reachable immeaditaly after current is executed)

        All statements in list are simple statements (no if/do blocks)
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

        Is used in compound statements to fixup links of preceding statements
        MUST be called after complementary set_next
        """
        self._prev = stmt

    def find_break_stmts(self):
        """Finds all BreakStmt instances in current scope (statement and sub-statements)

        For most statements, does nothing. TO be overloaded in block statements.
        Returns (possibly deep) list of BreakStmt objects
        """
        return []

    SettlePass = enum('PRE', 'POST_MINI')

    def settle(self, pass_no):
        """Settles Stmt object, must be called after all statements in proctype have been parsed

        Actually this is usable for statements that depend on other statements only
        There are currently 2 settle passes:
        1. Right after adding all statements
        2. After minimization (throwing away omittables)

        Arguments:
        - `pass_no`: settle pass number
        """
        pass

    def next_reduced(self):
        """Calculates next statements in reduced (minimized) graph
 
        Returns: tuple (
        (1) is valid endstate (True or None),
        (2) ends atomic (bool or None),
        (3) ends d_step (bool or None)
        (3) next statements (list)
        )

        Deduces whether current statement ends atomic/d_step context or is a valid endstate
        """
        ends_atomic = None
        ends_dstep = None
        endstate = None
        next_stmts = []

        # 1) if all next statements are omittable and end atomic context, True
        # 2) if each of next statements either does not end atomic context or is not omittable, False
        # Error otherwise (when there are some omittable statement that end atomic, but not all)
        def deduce_atomic(acc, e):
            if acc is not None and acc != e:
                raise RuntimeError, "Cannot reduce statement atomicity context"
            return e or acc

        for stmt in self._next:
            if stmt.omittable:
                es, ea, ed, n = stmt.next_reduced()
                # Deduce atomic and d_step context for current statement
                ends_atomic = deduce_atomic(ends_atomic, ea)
                ends_dstep = deduce_atomic(ends_dstep, ed)
                next_stmts += n
                # If any of reachable omittable statements is valid endstate,
                # this statement should also be endstate
                endstate = es or endstate
            else:
                # Next non-omittable statements do not affect atomicity
                ends_atomic = deduce_atomic(ends_atomic, False)
                ends_dstep = deduce_atomic(ends_dstep, False)
                next_stmts.append(stmt)

        return ((self.endstate or endstate),
                (self.ends_atomic or ends_atomic),
                (self.ends_dstep or ends_dstep),
                next_stmts)

    def minimize(self):
        """Minimizes statement graph, fixing _next to point to non-omittables

        Is called for all statements, including omittables themselves
        Should be called after settle(PRE)
        Ignores _prev!

        Updates atomicity and endstate validness
        """
        endstate, ends_atomic, ends_dstep, self._next = self.next_reduced()
        if not self.omittable:
            self.set_atomic(None, ends_atomic)
            self.set_dstep(None, ends_dstep)
            self.set_endstate(endstate)


class NoopStmt(Stmt):
    """Does nothing. Differs from base Stmt only in name
    """
    def __init__(self, name, omittable=False):
        """

        Arguments:
        - `name`: state name (str), used for debug printing
        """
        super(NoopStmt, self).__init__()
        self._name = name
        self._omittable = omittable

    def debug_repr(self):
        return self._name


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

    def debug_repr(self):
        return "%s = %s" % (self._varref, self._expr)


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

    def debug_repr(self):
        return "%s%s" % (self._op, self._varref)


class GotoStmt(Stmt):
    """Goto statement

    Always executable, does nothing. Is't next statement in label it's pointing to
    """

    def __init__(self, label):
        """

        Arguments:
        - `label`: Label object
        """
        Stmt.__init__(self)
        self._label = label
        self._omittable = True

    def debug_repr(self):
        return "goto %s" % self._label

    def settle(self, pass_no):
        # Will be called for 1st pass only
        self.set_next(self._label.parent_stmt)


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

    def debug_repr(self):
        return str(self._expr)


class ElseStmt(Stmt):
    """Else statement

    This is an expression that is 1 when all other branches are non-executable
    Actual expression (`cond`) is set by parent if/do statement
    """

    def __init__(self):
        Stmt.__init__(self)
        self.cond = None
        # BUG self._omittable = True

    def executable(self):
        if self.cond is None:
            raise RuntimeError, "`else' not in guard"
        return self.cond

    def debug_repr(self):
        return "else"


class BreakStmt(Stmt):
    """Break statement

    Always executable, does nothing
    """
    def __init__(self):
        super(BreakStmt, self).__init__()
        self._omittable = True

    def find_break_stmts(self):
        return [self]

    def debug_repr(self):
        return "break"


class AssertStmt(Stmt):
    """Assertion statement

    Always executable
    """
    #BUG: omittable, join with previous statement

    def __init__(self, expr):
        """

        Arguments:
        - `expr`: Expr object whose value is asserted to be != 0
        """
        Stmt.__init__(self)
        self._expr = expr

    def execute(self):
        return "ASSERT(%s, \"%s\")" % (self._expr.code(), self._expr)

    def debug_repr(self):
        return "assert(%s)" % self._expr


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
        self._omittable = True
        self._has_else = False
        for branch in options:
            if type(branch[0]) is ElseStmt:
                if self._has_else:
                    raise RuntimeError, "Multiple `else' branches"
                # This MUST be called before `has_else` is set to True, otherwise `cond` will always be "!1"
                branch[0].cond = "(!%s)" % (self.executable())
                self._has_else = True

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
        return "(%s)" % " || ".join([branch[0].executable() for branch in self._options
                                     if type(branch[0]) is not ElseStmt])

    def set_atomic(self, starts, ends):
        for branch in self._options:
            branch[0].set_atomic(starts, None)
            branch[-1].set_atomic(None, ends)
            
    def set_dstep(self, starts, ends):
        for branch in self._options:
            branch[0].set_dstep(starts, None)
            branch[-1].set_dstep(None, ends)

    def debug_repr(self):
        return "if"


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

    def debug_repr(self):
        return "do"


class SequenceStmt(Stmt):
    """Placeholder for a sequence of statements

    Executable when first sub-statement is executable
    Executes as no-op
    """

    def __init__(self, stmts):
        """

        Arguments:
        - `stmts`: list of Stmt objects
        """
        Stmt.__init__(self)
        self._stmts = stmts
        self._next = [stmts[0]]
        self._omittable = True

    def set_next(self, stmt):
        self._stmts[-1].set_next(stmt)

    def set_prev(self, stmt):
        self._prev = self._stmts[0].prev
        self._prev.set_next(self)
        stmt.set_next(self)

    def set_atomic(self, starts, ends):
        self._stmts[0].set_atomic(starts, None)
        self._stmts[-1].set_atomic(None, ends)

    def set_dstep(self, starts, ends):
        self._stmts[0].set_dstep(starts, None)
        self._stmts[-1].set_dstep(None, ends)

    def executable(self):
        return self._stmts[0].executable()

    def debug_repr(self):
        return "-(-"


class AtomicStmt(SequenceStmt):
    """Atomic statement sequence

    This is a dumb statement, needed only to set starts_atomic/ends_atomic
    flags on it's children
    """

    def __init__(self, stmts):
        """

        Arguments:
        - `stmts`: list of Stmt objects
        """
        super(AtomicStmt, self).__init__(stmts)
        self.set_atomic(True, True)

    def debug_repr(self):
        return "atomic"


class DstepStmt(SequenceStmt):
    """Deterministic step (d_step) statement sequence

    This is a dumb statement, needed only to set starts_dstep/ends_dstep
    flags on it's children

    Is *not* omittable (to always have a single start point)
    """

    def __init__(self, stmts):
        """

        Arguments:
        - `stmts`: list of Stmt objects
        """
        super(DstepStmt, self).__init__(stmts)
        # Some magic here
        # DstepStmt was meant to be like AtomicStmt but then was decided
        # to be made non-omittable, so that we always have single entry point in it
        # Therefore, _starts_dstep is set manually to be True,
        # while children don't actually start d_step
        self.set_dstep(None, True)
        self._starts_dstep = True
        self._omittable = False

    def debug_repr(self):
        return "d_step BEGIN"


class PrintStmt(Stmt):
    """Prints message to log

    Always executable
    """

    def __init__(self, fmt_string, args):
        """
        :arg fmt_string Printf-like format string
        :arg args list of Expr objects to pass to printf()
        """
        super(PrintStmt, self).__init__()
        self._args = args or []
        self._fmt_string = fmt_string

    def execute(self):
        printf_args = [self._fmt_string]
        printf_args += [e.code() for e in self._args]
        return 'PRINTF(%s)' % (', '.join(printf_args))

    def debug_repr(self):
        return 'printf'


class SendStmt(Stmt):
    """Sends data to channel

    Executable when channel not full
    """
    
    def __init__(self, chan_ref, arg_list):
        """
        
        Arguments:
        - `chan_ref`: (VarRef) channel reference
        - `arg_list`: list of Expression objects
        """
        super(SendStmt, self).__init__()
        self._chan_ref = chan_ref
        self._chan = chan_ref.deref()
        self._arg_list = arg_list
        if type(self._chan) is not Channel:
            raise RuntimeError, "Must be a channel"
        self._chan.check_args(arg_list)
        
    def executable(self):
        return ChanOpExpr('nfull', self._chan_ref).code()

    def execute(self):
        send_code_tpl = "$send_ops; CHAN_SEND($chan)"
        send_op_tpl = "$field_ref = $value"
        send_ops = []
        chan = self._chan_ref.code()
        chan_len = ChanOpExpr('len', self._chan_ref).code()
        for i, arg in enumerate(self._arg_list):
            send_ops.append(Template(send_op_tpl).substitute(field_ref=self._chan.field_ref(chan_len, i),
                                                             value=arg.code()))
        return Template(send_code_tpl).substitute(chan=chan,
                                                  send_ops="; ".join(send_ops))

    def debug_repr(self):
        return "%s ! %s" % (self._chan.name, ", ".join([str(e) for e in self._arg_list]))
        
                            
class RecvStmt(SendStmt):
    """Receives data from channel
    
    Executable when channel not empty.
    _arg_list is a list of VarRef objects
    """
    
    def executable(self):
        return ChanOpExpr('nempty', self._chan_ref).code()

    def execute(self):
        recv_code_tpl = "CHAN_RECV($chan); $recv_ops"
        recv_op_tpl = "$var = $field_ref"
        recv_ops = []
        chan = self._chan_ref.code()
        chan_len = ChanOpExpr('len', self._chan_ref).code()
        for i, arg in enumerate(self._arg_list):
            recv_ops.append(Template(recv_op_tpl).substitute(field_ref=self._chan.field_ref(chan_len, i),
                                                             var=arg.code()))
        return Template(recv_code_tpl).substitute(chan=chan,
                                                  recv_ops="; ".join(recv_ops))

    def debug_repr(self):
        return "%s ? %s" % (self._chan.name, ", ".join([str(e) for e in self._arg_list]))


class CCodeStmt(Stmt):
    """Arbitrary C code
    """

    def __init__(self, c_cond, c_code):
        """
        Arguments:
        - `c_cond`: (str) C code with executable condition; if None, always executable
        - `c_code`: (str) C code to execute
        """
        super(CCodeStmt, self).__init__()
        self._c_cond = c_cond
        self._c_code = c_code

    def debug_repr(self):
        return self._c_code.replace('\n', ' ')

    def executable(self):
        return self._c_cond or "1"

    def execute(self):
        return self._c_code
        c_code_tpl = """
#undef TRANSITIONS
#define C_CODE_DEF
#include STATEGEN_FILE
#undef  C_CODE_DEF
                $code
#define C_CODE_UNDEF
#include STATEGEN_FILE
#undef  C_CODE_UNDEF
#define TRANSITIONS
"""
        return Template(c_code_tpl).substitute(code=self._c_code)
