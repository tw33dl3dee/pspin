#!/usr/bin/env python

from sys import argv
import briefstat


if __name__ == '__main__':
    L = []
    for log in argv[1:]:
        S,T,Sp,t = briefstat.extract_spin_stat(log)
        L.append((S, t))
    LS = sorted(L, key=lambda l: l[0])
    print "#stat\ttime"
    for l in LS:
        print "%d\t%.2f" % l

