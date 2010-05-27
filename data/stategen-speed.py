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
            Spin[modelname] = T/t
        else:
            S,T,M,R = briefstat.extract_emu_stat(log)
            Pspin[modelname] = T/R

    lastmodel = None
    for m in sorted(set.intersection(set(Spin.keys()), set(Pspin.keys()))):
        sp1 = Spin.get(m, 0)
        sp2 = Pspin.get(m, 0)
        print r"\textbf{%s} & %d & %.0f & %.0f & %.1f \\" % (((lastmodel != m[0]) and m[0] or ""), m[1], sp1, sp2, sp2/sp1)
        lastmodel = m[0]
