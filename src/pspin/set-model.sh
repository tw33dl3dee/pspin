#!/bin/sh

if [ $# -ne 1 ]; then
	echo "Usage: $(basename $0) FILE" 1>&2
	exit 1
fi

MODEL_FILE=$1
TARGET_FILE=test.pml

rm -f $TARGET_FILE
ln -s $MODEL_FILE $TARGET_FILE
touch $TARGET_FILE
