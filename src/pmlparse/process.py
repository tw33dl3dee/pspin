#
#

from variable import *
from statement import Stmt, NoopStmt
from string import Template


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

    def __str__(self):
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
        self.active = active
        self.name = name
        self._vars = dict()
        self._args = []
        self._labels = dict()
        self._stmts = []
        self._state_count = 0
        self._last_stmt = None
        self._end_stmts = []
        self.add_var(SpecialVariable("_pid", "pid", SimpleType('pid')))
        self.add_stmt(NoopStmt("-start-"))

    def __str__(self):
        return "`%s' (active: %d)\n<\targs: %s\ndecl:\n%s\n\tcode: \n%s\n" \
            % (self.name, self.active, self._args, self.decl(), "\n".join([str(s) for s in self._stmts]))

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
        decl_tpl = """struct Proc$name {
    $fields;
}"""
        # sort variables by name, then by base type alignment so that
        # they are aligned with minimal padding (size decreasing)
        fields = [decl
                  for v in sorted(sorted(self._vars.values()),
                                  key=lambda v: v.type.c_align(),
                                  reverse=True)
                  for decl in [v.decl()]
                  if decl]
        return Template(decl_tpl).substitute(name=self.name, fields = ";\n\t".join(fields))

    def reftype(self):
        """Return C-type name for proctype
        """
        return "struct Proc%s" % self.name

    def ref(self):
        """Returns C-code (str) to reference current process instance of this type
        """
        return "(%s *)current" % self.reftype()

    def transitions_init(self, varname):
        """Returns C-code (str) that initializes transitions for this proctype

        Arguments:
        - `varname`: name of C-array that stores transitions (str)
        """
        trans_init_tpl = "$trans = calloc(sizeof(int **), $state_count)"
        trans_init_from_tpl = "$trans[$ip_from] = calloc(sizeof(int *), $to_count)"
        trans_add_tpl = "$trans[$ip_from][$i] = $ip_to\t/* $descr */"
        lines = [Template(trans_init_tpl).substitute(trans=varname, state_count=self._state_count)]
        for stmt in self._stmts:
            lines.append(Template(trans_init_from_tpl).substitute(trans=varname, ip_from=stmt.ip,
                                                                  to_count=(len(stmt.next) + 1)))
            for (i, next_stmt) in enumerate(stmt.next):
                lines.append(Template(trans_add_tpl).substitute(trans=varname, ip_from=stmt.ip, ip_to=next_stmt.ip,
                                                                i=i, descr=str(next_stmt)))
            lines.append(Template(trans_add_tpl).substitute(trans=varname, ip_from=stmt.ip, ip_to=0,
                                                            i=len(stmt.next), descr="END"))
        return ";\n".join(lines)

    def transitions(self):
        """Returns C-code (str) that performs transition for current proctype and given ip
        """
        switch_tpl = "\tswitch ($ipvar) {"
        case_tpl = """\t\tcase $ip:
            if ($executable) {
                NEW_STATE();
                RECORD_STEP("$step_str");
                $pre_exec;
                $execute;
                $post_exec;
                goto passed;
            }
            goto blocked"""
        lines = [Template(switch_tpl).substitute(ipvar="dest_ip")]
                                                 # TODO: was self.lookup_var("_ip").ref())]
        for stmt in self._stmts:
            lines.append(Template(case_tpl).substitute(ip=stmt.ip, executable=stmt.executable(),
                                                       pre_exec=stmt.pre_exec() or "",
                                                       post_exec=stmt.post_exec() or "",
                                                       execute=stmt.execute(), step_str=str(stmt)))
        lines += ["\t\tdefault:\n\t\t\tassert(0)", "\t\t}"]
        return ";\n".join(lines)

    def state_init(self):
        """Returns C-code (str) to initialize new process structure for current proctype
        """
        init_var_tpl = '\t\t$init'
        lines = []
        for v in sorted(self._vars.values()):
            init = v.init()
            if init is not None:
                lines.append(Template(init_var_tpl).substitute(init=init))
        return ";\n".join(lines)

    def state_dump(self, errstream):
        """Returns C-code (str) that dumps current proctype's variables
        
        :arg errstream: if True, dump to error stream
        """
        dump_func = errstream and "eprintf" or "dump_dprintf"
        print_var_tpl = '\t\t$dump_func("\\t-\\t$varname: $format\\n", $varref)'
        print_ip_tpl = '\t\t$dump_func("\\t-\\t$varname: $format ", $varref)' 
        print_stmt_tpl =  '\t\tswitch($ipvar) {'
        print_1st_stmt_case_tpl = '\t\t\tcase $ip: $dump_func("{%s}\\n", "$step_str"); break'
        print_stmt_case_tpl = '\t\t\tcase $ip: $dump_func("{%s} after {%s}\\n", "$step_str", "$prev_step_str"); break'
        ip_var = self.lookup_var("_ip")
        lines = [Template(print_ip_tpl).substitute(format=ip_var.printf_format(),
                                                   varref=ip_var.printf_ref(),
                                                   varname=str(ip_var),
                                                   dump_func=dump_func)]
        lines.append(Template(print_stmt_tpl).substitute(ipvar=ip_var.ref()))
        for stmt in self._stmts:
            if stmt.prev:
                lines.append(Template(print_stmt_case_tpl).substitute(ip=stmt.ip, step_str=str(stmt),
                                                                      prev_step_str=str(stmt.prev),
                                                                      dump_func=dump_func))
            else:
                lines.append(Template(print_1st_stmt_case_tpl).substitute(ip=stmt.ip, step_str=str(stmt),
                                                                          dump_func=dump_func))
                
        lines += ["\t\t\tdefault: assert(0)", "\t\t}"]
        for v in sorted(self._vars.values()):
            if not v.name == "_ip":
                lines.append(Template(print_var_tpl).substitute(format=v.printf_format(),
                                                                varref=v.printf_ref(),
                                                                varname=str(v),
                                                                dump_func=dump_func))
        return ";\n".join(lines)

    def valid_endstate_ips(self):
        """Return C-code (str) with array of valid endstate IP values for this proctype
        """
        valid_ips_tpl = '(int []){ $ips }'
        valid_ips = [str(stmt.ip) for stmt in self._end_stmts]
        valid_ips.append(str(-1))
        return Template(valid_ips_tpl).substitute(ips=', '.join(valid_ips))

    def add_stmt(self, stmt):
        """Adds new statement (not necessarily from topmost block) to process

        Sets `ip` for `stmt`

        Arguments:
        - `stmt`: Stmt object
        """
        self._stmts.append(stmt)
        self._state_count += 1
        stmt.ip = self._state_count - 1
        stmt.parent_proc = self
        if self._last_stmt:
            self._last_stmt.set_next(stmt)
            stmt.set_prev(self._last_stmt)
        self._last_stmt = stmt
        return stmt

    def finish(self):
        """Settles Process object, must be called after all statements and declarations
        """
        end_stmt = NoopStmt("-end-")
        self.add_stmt(end_stmt)
        self._end_stmts.append(end_stmt)
        # Alignment of special vars is forced to maximum value
        # so that they appear at the beginning of field list
        self.add_var(Variable("_ip", SimpleType('byte', SimpleType.MAX_ALIGN)))
        self.add_var(Variable("_proctype", SimpleType('byte', SimpleType.MAX_ALIGN)))
        self.sanity_check()
        for stmt in self._stmts:
            stmt.settle()

    def sizeof(self):
        """Returns C-code (str) that evaluates to process data structure size
        """
        return "sizeof(%s)" % self.reftype()
