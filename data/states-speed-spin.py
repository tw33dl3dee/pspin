#!/usr/bin/env python

from sys import argv
import briefstat


if __name__ == '__main__':
    print "#stat\ttime"
    for log in argv[1:]:
        S,T,Sp,t = briefstat.extract_spin_stat(log)
        print "%d\t%.2f" % (S,t)

