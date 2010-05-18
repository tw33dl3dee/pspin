#!/bin/sh

HOST=mpi
REMOTE_PATH=work/pspin

tools/copy-to-mpi.sh $HOST $REMOTE_PATH
ssh $HOST "cd $REMOTE_PATH; ./run-mpi-job.sh"
tools/copy-from-mpi.sh $HOST $REMOTE_PATH
