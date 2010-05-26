#!/usr/bin/env python

from sys import argv
from math import sqrt
import briefstat


def mean(lst):
    return float(sum(lst))/len(lst)
    
def stddev(lst):
    m = mean(lst)
    dev = sum([(l - m)**2 for l in lst])
    return sqrt(dev/(len(lst) - 1))


if __name__ == '__main__':
    L = []
    for i,log in enumerate(argv[1:]):
        S,T,M,R,I,t = briefstat.extract_stat(log)
        L.append((i,float(sum(M))/sum(T), stddev(S)/mean(S), mean(I), t))
    print "#type\tmsg%\tmem\tidle\ttotal"
    for l in L:
        print "%d\t%.2f\t%.3f\t%.2f\t%.2f" % l

