#
#

class Type(object):
    """
    """

    c_types = {'bit': 'unsigned', 'bool': 'unsigned', 'byte': 'unsigned char', 'short': 'short', 'int': 'int', 'pid':'char'}
    c_sizes = {'bit': 1, 'bool': 1}
    
    def __init__(self, name):
        """
        
        Arguments:
        - `name`:
        """
        if not name in self.c_types:
            raise RuntimeError, "Unknown type `%s'" % name
        self._name = name

    def __repr__(self):
        """
        """
        return self.name

    def c_type(self):
        return self.c_types[self._name]

    def c_bitsize(self):
        return self.c_sizes.get(self._name)


class Variable(object):
    """
    """
    
    def __init__(self, name, type, arrsize = None, initval = None):
        """

        Arguments:
        - `name`:
        - `type`:
        - `initval`:
        """
        self.name = name
        self.type = type
        self.arrsize = arrsize
        self.initval = initval
        self.parent = None

    def __repr__(self):
        return self.name

    def decl(self):
        bitspec = self.type.c_bitsize() and " : %d" % self.type.c_bitsize() or ""
        lenspec = self.arrsize and "[%d]" % self.arrsize or ""
        # TODO: fold bit arrays
        return "%s %s %s" % (self.type.c_type(), self.name, lenspec or bitspec)

    def ref(self):
        if self.parent:
            return "((%s)->%s)" % (self.parent.ref(), self.name)
        else:
            return "(%s)" % self.name

