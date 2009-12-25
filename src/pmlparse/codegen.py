#
#

from process import Process
from variable import *


class Codegen(object):
    """Main code generation API
    """
    def __init__(self):
        self._vars = dict()
        self._procs = []
        self.cur_proc = None
        self.add_var(Variable('_nproc', Type('byte'), len(self._procs)))
        self.add_var(Variable('_svsize', Type('short')))

    def __repr__(self):
        return "State: \n%s\nProcs: %s\n" % (self.state_decl(), self._procs)
        
    def start_proc(self, active, name):
        """Starts new proctype definition
        
        Arguments:
        - `active`: active count or 0 if not active,
        - `name`: proctype name
        """
        self.cur_proc = Process(active, name)
        self._procs.append(self.cur_proc)
        return self.cur_proc
        
    def end_proc(self):
        """Ends current proctype definition
        """
        self.cur_proc = None

    def add_var(self, var, vartype = None):
        """Adds variable to current scope

        Variable is added either to global symbol table or current proctype, if one exists.

        Arguments:
        - `var`: Variable object
        - `vartype`: Type object
        """
        if vartype is not None:
            var.type = vartype
        if self.cur_proc is not None:
            return self.cur_proc.add_var(var)
        elif var.name in self._vars:
            raise RuntimeError, "Redefinition: `%s'" % var.name
        else:
            self._vars[var.name] = var
            return var

    def lookup_var(self, name):
        """Lookups Variable object by name for current scope

        Variable is looked up either in global symbol table or current proctype, if one exists.

        Arguments:
        - `name`: variable name (str)
        """
        local = self.cur_proc and self.cur_proc.lookup_var(name)
        if local:
            return local
        elif name in self._vars:
            return self._vars[name]
        else:
            raise RuntimeError, "Undefined variable: `%s'" % name

    def state_decl(self):
        """Return C-code that declares global state structure
        """
        state_vars = self._vars.values()
        return "struct State {\n\t%s;\n}" % ";\n\t".join([v.decl() for v in state_vars])
