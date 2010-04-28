#
#

from utils import property3


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


class BuiltinType(Type):
    """Built-in type (can be represented with built-in C types)

    Arrays and bit-fields do count as built-in, too.
    """
    
    c_types = {'bit': 'unsigned', 'bool': 'unsigned', 'byte': 'unsigned char',
               'short': 'short', 'int': 'int', 'pid':'char'}
    c_bitsizes = {'bit': 1, 'bool': 1}
    # Need not be actual alignments, see c_align()
    c_aligns = {'unsigned':4, 'int':4, 'short':2, 'unsigned char':1, 'char':1}
    # Maximum possible alignment (used for special variable to enforce order)
    MAX_ALIGN = 256

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
        """C-type corresponding to this type (str)
        """
        return self.c_types[self._name]

    def c_align(self):
        """Not actual align (depends on platform) but score telling
        how this type is expected to be aligned

        Bigger values mean higher alignment requirement
        """
        return self._align or self.c_aligns[self.c_type()]

    def c_bitsize(self):
        """Bit-size of C type corresponding to this type (int)

        Returns 0 if type has no fixed bit-size.
        """
        return self.c_bitsizes.get(self._name)

    def printf_format(self):
        """printf specifier to use for this type (str)
        """
        return self.printf_codes.get(self._name, '%d')

    def printf_type(self):
        """C-type to pass to printf (str)
        """
        return self.printf_types.get(self._name, 'int')


class SimpleType(BuiltinType):
    """Simple type (from PROMELA's point of view)

    Doesn't differ from built-in type, really
    """
    pass


class ChanType(Type):
    """Channel type is actually a pointer to state area
    where channel data is stored
    """
    def __init__(self):
        # As state size is "short", any part of it can be addressed with it
        super(ChanType, self).__init__("short")


#############################################################


class Variable(object):
    """Variable object
    """

    def __init__(self, name, vartype, arrsize = None, initval = None):
        """

        Arguments:
        - `name`: variable name
        - `vartype`: Type object
        - `arrsize`: size of array (None if variable is not an array)
        - `initval`: initial value (or None)
        """
        self._name = name
        self._arrsize = arrsize
        self._initval = initval
        self._type = vartype
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

    def set_type(self, vartype):
        """Changes variable type
        """
        self._type = vartype
        self.check_type()

    def check_type(self):
        """Used for type validation
        """
        if not type(self._type) is SimpleType:
            raise RuntimeError, "Invalid type `%s' for `%s'" % (self._type, self._name)

    def decl(self):
        """Generates C-code for variable declaration
        """
        bitspec = self._type.c_bitsize() and " : %d" % self._type.c_bitsize() or ""
        lenspec = self._arrsize and "[%d]" % self._arrsize or ""
        # TODO: fold bit arrays
        return "%s %s %s" % (self._type.c_type(), self._name, lenspec or bitspec)

    def init(self):
        """Generates  C-code to initialize variable
        """
        if self._initval is None:
            return None
        else:
            return "%s = %s" % (self.ref(), self._initval)

    def ref(self):
        """Generates C-expression that references variable
        """
        if self.parent:
            return "((%s)->%s)" % (self.parent.ref(), self._name)
        else:
            return "(%s)" % self._name

    def printf_format(self):
        """Generates string to be used as printf-format specifier
        """
        skip = " "*(10 - len(self._name))
        if self._arrsize:
            return skip + "[%s]" % (", ".join([self._type.printf_format()]*self._arrsize))
        else:
            return skip + self._type.printf_format()

    def printf_ref(self):
        if self._arrsize:
            return ",".join(["(%s)%s[%d]" % (self._type.printf_type(), self.ref(), i)
                             for i in range(self._arrsize)])
        else:
            return "(%s)%s" % (self._type.printf_type(), self.ref())


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

    Channel data: [size(1 byte), entry #1(all values w/o align), entry #2...]
    Channels of size zero are not yet supported.
    """
    
    def __init__(self, name, size, typelist):
        """
        
        Arguments:
        - `size`: (int) size, positive
        - `typelist`: list of Type objects
        """
        super(Channel, self).__init__(name, ChanType())
        self._size = size
        self._typelist = typelist

    def check_type(self):
        """Used for type validation
        """
        if not type(self._type) is ChanType:
            raise RuntimeError, "Invalid type `%s' for `%s'" % (self._type, self._name)

    def init(self):
        """Generates  C-code to initialize variable
        """
        if self._initval is None:
            return None
        else:
            return "%s = %s" % (self.ref(), self._initval)

    def printf_format(self):
        """Generates string to be used as printf-format specifier
        """
        return NotImplemented

    def printf_ref(self):
        return NotImplemented
