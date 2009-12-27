#!/usr/bin/env python

from __future__ import with_statement
import pyggy_priv as pyggy
import sys
from pprint import pprint
from codegen import Codegen


def print_errpos(fname, lineno, charno, spaces_per_tab):
    with open(fname, "r") as src:
        print >>sys.stderr, src.readlines()[lineno - 1].replace("\t", ' ' * spaces_per_tab).rstrip()
    print >>sys.stderr, ' ' * (charno - 2), '^'


fname = sys.argv[1]
l,ltab = pyggy.getlexer("promela.pyl")
p,ptab = pyggy.getparser("promela.pyg")
l.setinput(fname)
p.setlexer(l)

l.SPACES_PER_TAB = 4

# while 1:
#     x = l.token()
#     print x, l.value
#     if x is None:
#         break

try:
    tree = p.parse()
except pyggy.errors.ParseError, e:
    print >>sys.stderr, "%s:%d:%d: %s (token type: %s) unexpected here" % (fname, l.lineno, l.charno, e.str, e.tok)
    print_errpos(fname, l.lineno, l.charno, l.SPACES_PER_TAB)
    sys.exit(1)
else:
    try:
        ptab.codegen = Codegen()
        code = pyggy.proctree(tree, ptab)
    except pyggy.errors.SemanticError, e:
        # Character position in semantic diagnostic doesn't look nice
        print >>sys.stderr, "%s:%d: %s" % (fname, e.lineno(l), e.err)
        print_errpos(fname, e.lineno(l), e.charno(l), l.SPACES_PER_TAB)
        sys.exit(2)
    else:
        code.write_file(sys.argv[2])
