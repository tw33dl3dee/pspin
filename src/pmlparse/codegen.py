#
#

from __future__ import with_statement
from process import Process
from variable import *
from string import Template


class Codegen(object):
    """Main code generation API
    """
    def __init__(self):
        self._vars = dict()
        self._procs = []
        self.cur_proc = None

    def write_file(self, fname):
        """Writes out generated code to file

        Arguments:
        - `fname`: file name to write to
        """
        with file(fname, "w") as f:
            self.write_block(f, 'STATE_DECL', self.state_decl())
            self.write_block(f, 'STATE_DUMP', self.state_dump())
            self.write_block(f, 'STATE_INIT', self.state_init())
            self.write_block(f, 'PROC_DECL', self.proc_decl())
            self.write_block(f, 'PROCSTATE_DUMP', self.procstate_dump())
            self.write_block(f, 'PROCSTATE_INIT', self.procstate_init())
            self.write_block(f, 'VALID_ENDSTATES', self.valid_endstates())
            self.write_block(f, 'TRANSITIONS_INIT', self.transitions_init())
            self.write_block(f, 'TRANSITIONS', self.transitions())

    def write_block(self, f, guard, code):
        """Writes block of code inside #ifdef/#endif guard

        Arguments:
        - `f`: file object
        - `guard`: macro checked with #ifdef
        - `code`: code (str)
        """
        f.write("\n#ifdef %s\n\n" % guard)
        f.write(code.replace("\t", " "*4))
        f.write(";\n\n#endif // %s\n" % guard)

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
        self.cur_proc.finish()
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
            var.parent = self
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
        state_tpl = """
#define STATESIZE(state) ((state)->_svsize)
#define STATEATOMIC(state) ((state)->_atomic)

struct State {
    $fields;
}"""
        # sort variables by name, then by base type alignment so that
        # they are aligned with minimal padding (size decreasing)
        fields = [v.decl() for v in sorted(sorted(self._vars.values()),
                                           key=lambda v: v.type.c_align(),
                                           reverse=True)]
        fields.append("char _procs[0]")
        return Template(state_tpl).substitute(fields = ";\n\t".join(fields))

    def state_ref(self):
        """Returns C-code (str) to reference global state structure
        """
        return "(struct State *)state"

    ref = state_ref

    def proc_decl(self):
        """Returns C-code which declares proctypes structures and their sizes
        """
        # TODO: take these varnames from symtable, do not hardcode
        procsizes_tpl = """
#define NPROCTYPE $nproctype
#define PROCIP(process) (process)->_ip
#define PROCTYPE(process) (process)->_proctype
#define PROCSIZE(process) procsizes[(process)->_proctype]

static size_t procsizes[] = { $procsizes };
static int procactive[] = { $procactive }"""
        procsizes = ", ".join([p.sizeof() for p in self._procs])
        procactive = ", ".join([str(p.active) for p in self._procs])
        lines = [p.decl() for p in self._procs]
        lines.append(Template(procsizes_tpl).substitute(nproctype=len(self._procs),
                                                        procsizes=procsizes, procactive=procactive))
        return ";\n".join(lines)

    def transitions_init(self):
        """Returns C-code (str) that initializes transitions for all proctypes
        """
        trans_init_tpl = "transitions = calloc(sizeof(int ***), $proc_count)"
        lines = [Template(trans_init_tpl).substitute(proc_count=len(self._procs))]
        lines += [proc.transitions_init("transitions[%d]" % i) for (i, proc) in enumerate(self._procs)]
        return ";\n".join(lines)

    def transitions(self):
        """Returns C-code (str) that performs transition for given (proctype, ip)
        """
        lines = ["switch (current->_proctype) {"]
        case_tpl = """case $proctype: {
    $switch;
    }
    break"""
        for (i, p) in enumerate(self._procs):
             lines.append(Template(case_tpl).substitute(proctype=i, switch=p.transitions()))
        lines += ["default:\n\tassert(0)", "}"]
        return ";\n".join(lines)

    def state_dump(self):
        """Returns C-code (str) that dumps current global state variables
        """
        print_var_tpl = 'dump_dprintf("-\\t$varname:$format\\n", $varref)'
        lines = []
        for v in self._vars.values():
            lines.append(Template(print_var_tpl).substitute(format=v.printf_format(),
                                                            varref=v.printf_ref(),
                                                            varname=str(v)))
        return ";\n".join(lines)

    def state_init(self):
        """Returns C-code (str) that initializes global state variables
        """
        lines = []
        for v in sorted(self._vars.values()):
            init = v.init()
            if init is not None:
                lines.append(init)
        return ";\n".join(lines)

    def procstate_dump(self):
        """Returns C-code (str) that dumps state variables of given proctype
        """
        lines = ["switch (current->_proctype) {"]
        case_tpl = """case $proctype: {
$dump;
    }
    break"""
        for (i, p) in enumerate(self._procs):
             lines.append(Template(case_tpl).substitute(proctype=i, dump=p.state_dump()))
        lines += ["default:\n\tassert(0)", "}"]
        return ";\n".join(lines)

    def procstate_init(self):
        """Returns C-code (str) that initializes state variables of given proctype
        """
        lines = ["switch (current->_proctype) {"]
        case_tpl = """case $proctype: {
$init;
    }
    break"""
        for (i, p) in enumerate(self._procs):
             lines.append(Template(case_tpl).substitute(proctype=i, init=p.state_init()))
        lines += ["default:\n\tassert(0)", "}"]
        return ";\n".join(lines)

    def valid_endstates(self):
        """Returns C-code (str) with array of valid endstate IP values of all proctypes
        """
        valid_endstates_tpl = "static int *valid_endstates[] = { $endstates }"
        endstates = ', '.join([p.valid_endstate_ips() for p in self._procs])
        return Template(valid_endstates_tpl).substitute(endstates=endstates)

    def finish(self):
        """Settles Codegen object, must be called after all proctypes and declarations
        """
        self.add_var(Variable('_svsize', Type('short')))
        self.add_var(Variable('_atomic', Type('pid'), initval=-1))
