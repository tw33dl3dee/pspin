#!/usr/bin/env python

from __future__ import with_statement
import pyggy_priv as pyggy
import sys
from pprint import pprint
from codegen import Codegen
from subprocess import Popen, PIPE


def pp_file(fname):
    return Popen(["cpp", fname] + pp_opt, stdout=PIPE).stdout

def print_errpos(fname, lineno, charno, spaces_per_tab):
    with pp_file(fname) as src:
        print >>sys.stderr, src.readlines()[lineno - 1].replace("\t", ' ' * spaces_per_tab).rstrip()
    print >>sys.stderr, ' ' * (charno - 2), '^'


fname = sys.argv[1]
out_fname = sys.argv[2]
dot_fname = sys.argv[3]
pp_opt = sys.argv[4:]

l,ltab = pyggy.getlexer("promela.pyl")
p,ptab = pyggy.getparser("promela.pyg")
l.setinput(pp_file(fname))
p.setlexer(l)

l.SPACES_PER_TAB = 4

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
        code.write_file(out_fname)
        code.write_dot(dot_fname)
