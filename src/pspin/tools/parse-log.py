#!/usr/bin/env python
#

from sys import argv
import re


stat_regex = r'\[(\d+)\] BRIEF S(\d+) T(\d+) M(\d+) R([\d\.]+) I([\d\.]+)'

def dict_to_list(d):
    return [v for k,v in sorted(d.iteritems(), key=lambda kv: kv[0])]

def parse_log(lines):
    S = {}
    T = {}
    M = {}
    R = {}
    I = {}
    for line in lines:
        m = re.match(stat_regex, line) 
        if m:
            node = int(m.group(1))
            S[node] = m.group(2)
            T[node] = m.group(3)
            M[node] = m.group(4)
            R[node] = m.group(5)
            I[node] = m.group(6)
    print 'S:', dict_to_list(S) 
    print 'T:', dict_to_list(T) 
    print 'M:', dict_to_list(M) 
    print 'R:', dict_to_list(R) 
    print 'I:', dict_to_list(I) 


fname = argv[1]

if __name__ == '__main__':
    with open(fname) as f:
        parse_log(f.readlines())
