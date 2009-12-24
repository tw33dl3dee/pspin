#
#

from variable import *
from pprint import pformat
from statement import Stmt


class Label(object):
    """Process label object
    """
    
    def __init__(self, name, parent):
        """
        
        Arguments:
        - `name`: label name
        - `parent`: Process object
        """
        self._name = name
        self._parent = parent
        # TODO: determine dynammically?..
        self.ip = "%s_IP" % str(self)

    def __repr__(self):
        return "%s_%s"% (self._parent.name, self._name)


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
        self._labels = []
        self.add_var(Variable("_pid", Type('pid')))
        self.add_var(Variable("_ip", Type('byte')))

    def __repr__(self):
        return "`%s' (active: %d)\n<\targs: %s\ndecl:\n%s\n\tlabels: %s\n\tcode: %s>" \
            % (self.name, self._active, self._args, self.decl(), self._labels, \
                   pformat(self._stmts))

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

    def set_body(self, stmts):
        """
        
        Arguments:
        - `stmts`:
        """
        self._stmts = stmts

    def add_label(self, label):
        """Add label to process
        
        Arguments:
        - `label`: Label object
        """
        self._labels.append(label)

    def lookup_label(self, name):
        """Return Label object belonging to this process
        
        Arguments:
        - `name`: label name
        """
        return Label(name, self)

    def decl(self):
        """Returns C-code (str) that declares structure with internal data for this proctype
        """
        return "struct Proc%s {\n\t%s;\n}" % (self.name, ";\n\t".join([v.decl() for v in self._vars.values()]))

    def ref(self):
        """Return C-code (str) to reference current process instance of this type
        """
        return "(Proc%s)current" % self.name
