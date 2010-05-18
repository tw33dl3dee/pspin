#!/bin/sh

IN_FILE_LIST="*.[ch] Makefile.bare pspin.job tools/run-mpi-job.sh"
HOST=$1
REMOTE_PATH=$2

scp $IN_FILE_LIST $HOST:$REMOTE_PATH
