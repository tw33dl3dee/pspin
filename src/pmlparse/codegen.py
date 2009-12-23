#
#

from process import Process


class Codegen(object):
    def __init__(self):
        self._vars = dict()
        self._procs = []
        self.cur_proc = None

    def __repr__(self):
        return "Vars: %s\nProcs: %s\n" % ([v.decl() for v in self._vars.values()], self._procs)
        
    def start_proc(self, active, name):
        """
        
        Arguments:
        - `active`: active count or 0 if not active,
        - `name`:
        """
        self.cur_proc = Process(active, name)
        self._procs.append(self.cur_proc)
        return self.cur_proc
        
    def end_proc(self):
        self.cur_proc = None

    def add_var(self, var, type = None):
        if type is not None:
            var.type = type
        if self.cur_proc is not None:
            return self.cur_proc.add_var(var)
        elif var.name in self._vars:
            raise RuntimeError, "Redefinition: `%s'" % var.name
        else:
            self._vars[var.name] = var
            return var

    def lookup_var(self, name):
        local = self.cur_proc and self.cur_proc.lookup_var(name)
        if local:
            return local
        elif name in self._vars:
            return self._vars[name]
        else:
            raise RuntimeError, "Undefined variable: `%s'" % name


