#
#

from utils import property3
from string import Template
from expression import ConstExpr


class Type(object):
    """Type object
    """

    def __init__(self, name):
        """
        Arguments:
        - `name`: type name (str)
        """
        self._name = name

    def __str__(self):
        return self._name

    def c_size(self):
        """Returns C code which evaluates to machine size of this type
        """
        return "sizeof(%s)" % self.c_type()

    def c_type(self):
        """C-type corresponding to this type (str)
        """
        raise NotImplementedError

    def c_align(self):
        """Not actual align (depends on platform) but score telling
        how this type is expected to be aligned

        Bigger values mean higher alignment requirement
        """
        raise NotImplementedError

    def c_bitsize(self):
        """Bit-size of C type corresponding to this type (int)

        Returns 0 if type has no fixed bit-size.
        """
        return 0

    def printf_format(self):
        """printf specifier to use for this type (str)
        """
        raise NotImplementedError

    def printf_ref(self, varref):
        """printf() argument for printing variable of given type

        Arguments:
        - `varref`: C code (str) with variable refernce
        """
        raise NotImplementedError


class BuiltinType(Type):
    """Built-in type (can be represented with built-in C types)

    Arrays and bit-fields do count as built-in, too.
    """

    c_types = {'bit': 'unsigned', 'bool': 'unsigned', 'byte': 'unsigned char',
               'short': 'short', 'int': 'int', 'pid':'char'}
    c_bitsizes = {'bit': 1, 'bool': 1}
    # Need not be actual alignments, see c_align()
    c_aligns = {'unsigned':4, 'int':4, 'short':2, 'unsigned char':1, 'char':1}
    # Maximum and minimum possible alignments (used for special variable to enforce order)
    MAX_ALIGN = 256
    MIN_ALIGN = 0

    printf_codes = {}  # no special cases here
    printf_types = {}  # no special cases here

    def __init__(self, name, align=None):
        """

        Arguments:
        - `align`: type alignment requirement (instead of default, given by c_aligns)
        """
        if not name in self.c_types:
            raise RuntimeError, "Unknown type `%s'" % name
        super(BuiltinType, self).__init__(name)
        self._align = align

    def c_type(self):
        return self.c_types[self._name]

    def c_align(self):
        # Bit fields go last
        if self.c_bitsize() is not None:
            return self.MIN_ALIGN
        return self._align or self.c_aligns[self.c_type()]

    def c_bitsize(self):
        return self.c_bitsizes.get(self._name)

    def printf_format(self):
        return self.printf_codes.get(self._name, '%d')

    def _printf_type(self):
        return self.printf_types.get(self._name, 'int')

    def printf_ref(self, varref):
        # For built-in types, this just printf varref prefixed with type cast
        return "(%s)%s" % (self._printf_type(), varref)


class SimpleType(BuiltinType):
    """Simple type (from PROMELA's point of view)

    Doesn't differ from built-in type, really
    """
    pass


class ChanType(BuiltinType):
    """Channel data is stored as byte array for now
    """
    def __init__(self):
        # Minimal align, so that channels go last
        super(ChanType, self).__init__("byte", 1)


class UserType(Type):
    """User-defined types (structures)
    """
    def __init__(self, name):
        super(UserType, self).__init__(name)
        self._fields = []

    def c_type(self):
        return "struct Utype%s" % str(self)

    def c_align(self):
        # Align by first field
        if len(self._fields):
            return self._fields[0].type.c_align()
        else:
            return 1

    def add_field(self, fieldvar):
        if fieldvar.hidden:
            raise RuntimeError, "Field cannot be hidden: `%s'" % fieldvar.name
        self._fields.append(fieldvar)

    def finish(self):
        pass

    def decl(self):
        utype_decl_tpl = """$hdr {
    $fields;
}
"""
        field_decls = ';\n\t'.join([f.decl() for f in sorted(sorted(self._fields),
                                                             key=lambda v: v.type.c_align(),
                                                             reverse=True)])
        return Template(utype_decl_tpl).substitute(hdr=self.c_type(),
                                                   fields=field_decls)

    def printf_format(self):
        return "{%s}" % (", ".join(["%s:%s" % (f, f.printf_format(1)) for f in self._fields]))

    def printf_ref(self, varref):
        # this prints printf() arguments to refence all fields, passing
        # to each field's printf_ref() it's reference via our reference
        return ", ".join([f.printf_ref("(%s.%s)" % (varref, f.ref())) for f in self._fields])


#############################################################


class Variable(object):
    """Variable object
    """

    def __init__(self, name, vartype, arrsize = None, initval = None):
        """

        Arguments:
        - `name`: variable name
        - `vartype`: Type object
        - `arrsize`: size of array (None if variable is not an array,
                                    otherwise must be an Expression that can be evaluated an generation time)
        - `initval`: initial value (Expression or None)
        """
        self._name = name
        self._arrsize = arrsize
        self._initval = initval
        self._type = vartype
        self._visible = None
        if arrsize and not arrsize.const:
            raise RuntimeError, "Array size must be constant"
        if vartype:
            self.check_type()
        self.parent = None  # parent ref()able object object

    def __str__(self):
        return self._name

    def __cmp__(self, other):
        return cmp(self._name, other.name)

    @property
    def name(self):
        return self._name

    @property
    def type(self):
        return self._type

    def set_visible(self, visible):
        """Sets variable visibility

        False: variable is hidden
        True: variable is tracked (currently not supported)
        None: usual variable
        """
        if visible:
            raise RuntimeError, "`%s': variable tracking is not supported" % self.name
        self._visible = visible

    @property
    def hidden(self):
        """Hidden variable is not stored in state vector
        """
        return self._visible is False

    def set_type(self, vartype):
        """Changes variable type
        """
        self._type = vartype
        self.check_type()

    def check_type(self):
        """Used for type validation
        """
        if not type(self._type) in (SimpleType, UserType):
            raise RuntimeError, "Invalid type `%s' for `%s'" % (self._type, self._name)

    def decl(self):
        """Generates C-code (sequence of str) for variable declaration
        """
        bitspec = self._type.c_bitsize() and " : %d" % self._type.c_bitsize() or ""
        lenspec = self._arrsize and "[%s]" % self._arrsize.code() or ""
        static = self.hidden and "static " or " "
        # TODO: fold bit arrays
        return "%s%s %s %s" % (static, self._type.c_type(), self._name, lenspec or bitspec)

    def init(self):
        """Generates  C-code to initialize variable
        """
        if self._initval is None:
            return None
        else:
            return "%s = %s" % (self.ref(), self._initval.code())

    def ref(self):
        """Generates C-expression that references variable
        """
        if self.parent:
            return "(%s)->%s" % (self.parent.ref(), self._name)
        else:
            return "%s" % self._name

    def printf_format(self, depth=0):
        """Generates string to be used as printf-format specifier
        """
        if depth == 0:
            skip = " "*(10 - len(self._name))
        else:
            skip = ""
        if self._arrsize:
            return skip + "[%s]" % (", ".join([self._type.printf_format()]*self._arrsize.eval()))
        else:
            return skip + self._type.printf_format()

    def printf_ref(self, selfref=None):
        """Generates C code with arguments to printf() for printing this variable

        Arguments:
        - `selfref`: how to reference outselves. If None, self.ref() is used

        When selfref is not None, it means that we are part of some bigger structure
        (e.g., array field inside a typedef)

        selfref is passed to our type's print_ref so that it can print our structure
        using this reference

        Fuck a fuck (C)
        """
        if selfref is None:
            selfref = self.ref()
        if self._arrsize:
            return ",".join([self.type.printf_ref("%s[%d]" % (selfref, i))
                             for i in range(self._arrsize.eval())])
        else:
            return self.type.printf_ref(selfref)


class SpecialVariable(Variable):
    """Special variable that is not stored in global/process state
    """

    def __init__(self, name, c_name, vartype):
        """

        Arguments:
        - `name`: variable name as used in Promela
        - `c_name`: variable name as used in C
        - `vartype`: Type object
        """
        super(SpecialVariable, self).__init__(name, vartype)
        self._c_name = c_name

    def decl(self):
        # Do not include in state declaration
        return None

    def init(self):
        # Do not initialize in state declaration
        return None

    def ref(self):
        return self._c_name


class Channel(Variable):
    """Channels variable holds a pointer (of type ChanType) to state area
    with channel data.

    Channel data: [len(1 byte), max len(1 byte), entry #1(all values w/o align), entry #2...]
    Channels of size zero are not yet supported.
    """

    def __init__(self, name, max_len, typelist):
        """

        Arguments:
        - `max_len`: (int) max length, positive
        - `typelist`: list of Type objects
        """
        self._max_len = max_len
        self._typelist = typelist
        # Dirty hack: chan_c_size is actually a string with C expression,
        #   so it cannot be evauluated as ConstExpr
        # But since we overload print_*, it's eval() is never called
        super(Channel, self).__init__(name, ChanType(), ConstExpr(self._chan_c_size()))

    def check_type(self):
        """Used for type validation
        """
        if not type(self._type) is ChanType:
            raise RuntimeError, "Invalid type `%s' for `%s'" % (self._type, self._name)

    def check_args(self, arg_list):
        """Checks list of send/recv arguments (VarRef or Expression objects)
        to match declaration
        """
        if len(arg_list) != len(self._typelist):
            raise RuntimeError, "Invalid number of arguments, %d expected" % len(self._typelist)

    def _chan_c_size(self):
        """C-code (str) which evaluates to full size of channel contents
        """
        chan_size_tpl = "(sizeof(struct Channel) + $entries*$entry_size)"
        return Template(chan_size_tpl).substitute(entries=self._max_len,
                                                  entry_size=self._entry_c_size())

    def _entry_c_size(self):
        """C-code (str) which
        """
        return self._field_offset(len(self._typelist))

    def _field_offset(self, field_idx):
        """C-code (str) which evaluates to offset of N-th field in channel entry
        """
        if field_idx == 0:
            return "0"
        else:
            return "(" + " + ".join([t.c_size() for t in self._typelist[0:field_idx]]) + ")"

    def field_ref(self, entry_idx, field_idx):
        """C-code (str) wich references M-th field of N-th channel entry

        Does not check channel current and max length
        """
        field_ref_tpl = "CHAN_FIELD($chan, $type, $entry_size, $entry_idx, $field_offset)"
        return Template(field_ref_tpl).substitute(chan=self.ref(),
                                                  type=self._typelist[field_idx].c_type(),
                                                  entry_size=self._entry_c_size(),
                                                  entry_idx=entry_idx,
                                                  field_offset=self._field_offset(field_idx))

    def init(self):
        init_tpl = "CHAN_LEN($chan) = 0, CHAN_MAXLEN($chan) = $max_len"
        return Template(init_tpl).substitute(chan=self.ref(), max_len=self._max_len)

    def printf_format(self):
        """Generates string to be used as printf-format specifier
        """
        printf_fmt_tpl = "$skip<%d of %d> [$fields_fmt]"
        skip = " "*(10 - len(self._name))
        entry_fmt = "{" + "; ".join([t.printf_format() for t in self._typelist]) + "}"
        fields_fmt = ", ".join([entry_fmt]*self._max_len)
        return Template(printf_fmt_tpl).substitute(skip=skip, fields_fmt=fields_fmt)

    def printf_ref(self):
        printf_ref_tpl = "(int)CHAN_LEN($chan), (int)CHAN_MAXLEN($chan), $fields"
        return Template(printf_ref_tpl).substitute(chan=self.ref(),
                                                   fields=", ".join([self._typelist[f].printf_ref(self.field_ref(e, f))
                                                                     for e in range(self._max_len)
                                                                     for f in range(len(self._typelist))]))

