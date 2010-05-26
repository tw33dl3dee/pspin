#!/usr/bin/env python
#

from sys import argv
import briefstat


def print_stat(logfile):
    S,T,M,R,I,t = briefstat.extract_stat(logfile)
    print 'States', ' '.join([str(s) for s in S])
    print 'Trans ', ' '.join([str(s) for s in T])
    print 'Msg   ', ' '.join([str(s) for s in M])
    print 'Run   ', ' '.join([str(s) for s in R])
    print 'Idle  ', ' '.join([str(s) for s in I])
    print 'Total ', t


if __name__ == '__main__':
    for log in argv[1:]:
        print_stat(log)
