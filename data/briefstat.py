#
#

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
            S[node] = int(m.group(2))
            T[node] = int(m.group(3))
            M[node] = int(m.group(4))
            R[node] = float(m.group(5))
            I[node] = float(m.group(6))
    t = int((I[1]+R[1])*100)/100.0
    return (dict_to_list(S), dict_to_list(T), dict_to_list(M),
            dict_to_list(R), dict_to_list(I), t)

def parse_spin_log(lines):
    state_rgx = r'\W*(\d+) states\, stored'
    time_rgx = r'pan: elapsed time ([\d\.]+) seconds'
    speed_rgx = r'pan: rate ([\d\.]+) states/second'
    S = 0
    T = 0
    Sp = 0
    t = 1
    for line in lines:
        m = re.match(state_rgx, line)
        if m: S = int(m.group(1))
        m = re.match(time_rgx, line)
        if m: t = float(m.group(1))
        m = re.match(speed_rgx, line)
        if m: Sp = float(m.group(1))
        
    return S,T,Sp,t

def extract_stat(fname):
    with open(fname) as f:
        return parse_log(f.readlines())

def extract_spin_stat(fname):
    with open(fname) as f:
        return parse_spin_log(f.readlines())
