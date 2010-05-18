#!/bin/sh

JOB_NAME=pspin.job

make pspin -f Makefile.bare || exit 1

rm -f pspin.std*

llsubmit $JOB_NAME || exit 1

while ! llq -x | grep -q 'no job' ; do
	llq -x
	sleep 5
done
