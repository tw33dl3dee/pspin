#!/bin/sh

if [ $# -ne 2 ]; then
	echo "Usage: $(basename $0) MODEL STATES"
	exit 1
fi

MODEL=$1
STATES=$2

#./set-model.sh models/$MODEL.pml
make mpirun
mv pspin.stdout.log experiments/pspin.$MODEL.$STATES.log
