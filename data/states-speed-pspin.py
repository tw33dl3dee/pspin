#!/usr/bin/env python

from sys import argv
import briefstat


if __name__ == '__main__':
    print "#stat\ttime"
    for log in argv[1:]:
        S,T,M,R,I,t = briefstat.extract_stat(log)
        print "%d\t%.2f" % (sum(S),t)
        
