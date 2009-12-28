#
#

class Type(object):
    """Type object
    """

    c_types = {'bit': 'unsigned', 'bool': 'unsigned', 'byte': 'unsigned char', 'short': 'short', 'int': 'int', 'pid':'char'}
    c_sizes = {'bit': 1, 'bool': 1}
    
    def __init__(self, name):
        """
        
        Arguments:
        - `name`: type name (str)
        """
        if not name in self.c_types:
            raise RuntimeError, "Unknown type `%s'" % name
        self._name = name

    def __str__(self):
        return self._name

    def c_type(self):
        """C-type corresponding to this type (str)
        """
        return self.c_types[self._name]

    def c_bitsize(self):
        """Bit-size of C type corresponding to this type (int)

        Returns 0 if type has no fixed bit-size.
        """
        return self.c_sizes.get(self._name)


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
        self.name = name
        self.type = vartype
        self.arrsize = arrsize
        self.initval = initval
        self.parent = None  # parent ref()able object object

    def __str__(self):
        return self.name

    def __cmp__(self, other):
        return cmp(self.name, other.name)

    def decl(self):
        """Generates C-code for variable declaration
        """
        bitspec = self.type.c_bitsize() and " : %d" % self.type.c_bitsize() or ""
        lenspec = self.arrsize and "[%d]" % self.arrsize or ""
        # TODO: fold bit arrays
        return "%s %s %s" % (self.type.c_type(), self.name, lenspec or bitspec)

    def ref(self):
        """Generates C-expression that references variable
        """
        if self.parent:
            return "((%s)->%s)" % (self.parent.ref(), self.name)
        else:
            return "(%s)" % self.name


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

    def ref(self):
        return self._c_name
