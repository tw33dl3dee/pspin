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

    def __repr__(self):
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
        self.parent = None

    def __repr__(self):
        return self.name

    def decl(self):
        """Generates C-code for variable declaration
        """
        bitspec = self.type.c_bitsize() and " : %d" % self.type.c_bitsize() or ""
        lenspec = self.arrsize and "[%d]" % self.arrsize or ""
        # TODO: fold bit arrays
        return "%s %s %s" % (self.type.c_type(), self.name, lenspec or bitspec)

    def ref(self):
        """Generates C-code for variable reference in expressions
        """
        if self.parent:
            return "((%s)->%s)" % (self.parent.ref(), self.name)
        else:
            return "(%s)" % self.name

