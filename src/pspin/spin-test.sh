#!/bin/sh

MODEL=test.pml

# FULLSTATE
spin -a $MODEL && gcc -DNOREDUCE -DSAFETY -DNOCOMP pan.c -o pan && ./pan -E -m1000000 $@
# BITHASH
#spin -a $MODEL && gcc -DNOREDUCE -DSAFETY -DNOCOMP -DBITSTATE pan.c -o pan && ./pan -E -m1000000 -w33 $@
rm pan*
