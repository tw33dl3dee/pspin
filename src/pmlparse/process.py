#
#

from variable import *
from pprint import pformat
from statement import Stmt, NoopStmt


class Label(object):
    """Process label object
    """
    
    def __init__(self, name):
        """
        
        Arguments:
        - `name`: label name
        """
        self._name = name
        self.parent_stmt = None

    def __repr__(self):
        return self._name


class Process(object):
    """Process object
    """
    
    def __init__(self, active, name):
        """
        
        Arguments:
        - `active`: active count (0 means inactive)
        - `name`: name (str)
        """
        self._active = active
        self.name = name
        self._vars = dict()
        self._args = []
        self._labels = dict()
        self._stmts = []
        self._state_count = 0
        self._last_stmt = None
        self.add_var(Variable("_pid", Type('pid')))
        self.add_stmt(NoopStmt())

    def __repr__(self):
        return "`%s' (active: %d)\n<\targs: %s\ndecl:\n%s\n\tlabels: %s\n\tcode: \n%s>" \
            % (self.name, self._active, self._args, self.decl(), self._labels, "\n".join([str(s) for s in self._stmts]))

    def lookup_var(self, name):
        """Lookup variable in process symbol table

        Arguments:
        - `name`: variable name (str)
        """
        if name in self._vars:
            return self._vars[name]
        else:
            return None

    def add_var(self, var):
        """Add variable to process symbol table

        Arguments:
        - `var`: Variable object
        """
        if var.name in self._vars:
            raise RuntimeError, "Redefinition: `%s'" % var.name
        else:
            self._vars[var.name] = var
            var.parent = self
            return var

    def set_args(self, varlist):
        """Add variables to list of process' arguments
        
        Arguments:
        - `varlist`: list of Variable objects
        """
        self._args = [var.name for var in varlist]

    # def set_body(self, stmts):
    #     """Defines topmost process block (by setting it's statements)
        
    #     Arguments:
    #     - `stmts`: list of Stmt objects
    #     """
    #     self._stmts = stmts
    #     self.check_body()

    def sanity_check(self):
        """Performs sanity checks (must be called after process is completely defined)
        """
        for label in self._labels.values():
            if label.parent_stmt is None:
                raise RuntimeError("Label used but not defined: %s" % label)

    def add_label(self, name):
        """Add label to process
        
        Arguments:
        - `label`: label name (str)
        """
        self._labels[name] = Label(name)
        return self._labels[name]

    def lookup_label(self, name):
        """Return Label object belonging to this process
        
        Arguments:
        - `name`: label name (str)
        """
        return self._labels.get(name) or self.add_label(name)

    def decl(self):
        """Returns C-code (str) that declares structure with internal data for this proctype
        """
        return "struct Proc%s {\n\t%s;\n}" % (self.name, ";\n\t".join([v.decl() for v in self._vars.values()]))

    def reftype(self):
        """Return C-type name for proctype
        """
        return "struct Proc%s" % self.name
    
    def ref(self):
        """Returns C-code (str) to reference current process instance of this type
        """
        return "(%s *)current" % self.reftype()

    def add_stmt(self, stmt):
        """Adds new statement (not necessarily from topmost block) to process

        Sets `ip` for `stmt`
        
        Arguments:
        - `stmt`: Stmt object
        """
        self._stmts.append(stmt)
        self._state_count += 1
        stmt.ip = self._state_count
        stmt.parent_proc = self
        if self._last_stmt:
            self._last_stmt.set_next(stmt)
            stmt.set_prev(self._last_stmt)
        self._last_stmt = stmt
        print "Added statement %s" % type(stmt)
        return stmt

    def finish(self):
        """Settles Process object, must be called after all statements and declarations
        """
        self.add_var(Variable("_ip", Type('byte')))
        self.sanity_check()
        for stmt in self._stmts:
            stmt.settle()
