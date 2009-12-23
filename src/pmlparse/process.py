#
#

from variable import *


class Process(object):
    """
    """
    
    def __init__(self, active, name):
        """
        
        Arguments:
        - `active`:
        - `name`:
        """
        self._active = active
        self._name = name
        self._vars = dict()
        self._args = []
        self.add_var(Variable("_pid", Type('pid')))

    def __repr__(self):
        return "`%s' (active: %d)\n<\targs: %s\n\tvars: %s\n\tcode: %s>" \
            % (self._name, self._active, self._args, [v.decl() for v in self._vars.values()], self._stmts)

    def lookup_var(self, name):
        if name in self._vars:
            return self._vars[name]
        else:
            return None

    def add_var(self, var):
        if var.name in self._vars:
            raise RuntimeError, "Redefinition: `%s'" % var.name
        else:
            self._vars[var.name] = var
            var.parent = self
            return var

    def set_args(self, varlist):
        """
        
        Arguments:
        - `varlist`:
        """
        self._args = [var.name for var in varlist]

    def set_body(self, stmts):
        """
        
        Arguments:
        - `stmts`:
        """
        self._stmts = stmts

    def ref(self):
        """
        """
        return "(Proc%s)current" % self._name
