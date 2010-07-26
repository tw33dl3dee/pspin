#
#

import sys


def listify(x):
    """Make scalar a single-element array"""
    if isinstance(x, list):
        return x
    else:
        return [x]


def enum(*sequential, **named):
    enums = dict(zip(sequential, range(len(sequential))), **named)
    return type('Enum', (), enums)


def flatten(a):
    """Flatten a list."""
    return bounce(flatten_k(a, lambda x: x))


def bounce(thing):
    """Bounce the 'thing' until it stops being a callable."""
    while callable(thing):
        thing = thing()
    return thing


def flatten_k(a, k):
    """CPS/trampolined version of the flatten function.  The original
    function, before the CPS transform, looked like this:

    def flatten(a):
        if not isinstance(a,(tuple,list)): return [a]
        if len(a)==0: return []
        return flatten(a[0])+flatten(a[1:])

    The following code is not meant for human consumption.
    """
    if not isinstance(a, (tuple, list)):
        return lambda: k([a])
    if len(a)==0:
        return lambda: k([])
    def k1(v1):
        def k2(v2):
            return lambda: k(v1 + v2)
        return lambda: flatten_k(a[1:], k2)
    return lambda: flatten_k(a[0], k1)


def property3(function):
    f_locals = {'doc':function.__doc__}
    def probeFunc(frame, event, _arg):
        if event == 'return':
            f_locals['fget'] = frame.f_locals.get('__get__')
            f_locals['fset'] = frame.f_locals.get('__set__')
            f_locals['fdel'] = frame.f_locals.get('__delete__')
            sys.settrace(None)
        return probeFunc
    sys.settrace(probeFunc)
    function(function)
    return property(**f_locals)


class Test(object):
    def __init__(self):
        self._prop = 0

    @property3
    def prop(self):
        def __set__(self, val):
            self._prop = val
            print "Set to %s" % val
        def __get__(self):
            return self._prop
        def __delete__(self):
            self._prop = None
