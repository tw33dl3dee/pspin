#!/usr/bin/env python

from sys import argv
import briefstat


if __name__ == '__main__':
    Spin = {}
    Pspin = {}
    for log in argv[1:]:
        tool,model,param,ext = briefstat.parse_log_name(log)
        modelname = (model.capitalize(), param)
        if tool == 'spin':
            S,T,Sp,t = briefstat.extract_spin_stat(log)
            Spin[modelname] = Sp
        else:
            S,T,M,R = briefstat.extract_emu_stat(log)
            Pspin[modelname] = S/R

    for m in sorted(set.intersection(set(Spin.keys()), set(Pspin.keys()))):
        sp1 = Spin.get(m, 0)
        sp2 = Pspin.get(m, 0)
        print r"\textbf{%s} (%d) & %.0f & %.0f \\" % (m[0], m[1], sp1, sp2)