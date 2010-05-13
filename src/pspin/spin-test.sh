#!/bin/sh

MODEL=test.pml

spin -a $MODEL
gcc -DNOREDUCE -DSAFETY -DNOCOMP pan.c -o pan
./pan -E -m100000
rm pan*