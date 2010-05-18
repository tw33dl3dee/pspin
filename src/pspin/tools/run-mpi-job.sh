#!/bin/sh

JOB_NAME=pspin.job

make pspin -f Makefile.bare

rm -f pspin.std*

llsubmit $JOB_NAME

while ! llq -x | grep 'no job' ; do
	llq -x
	sleep 5
done
