#!/bin/sh

JOB_NAME=pspin.job

rm -f pspin.std*

make pspin -f Makefile.bare || exit 1

llsubmit $JOB_NAME || exit 1

cleanup ()  {
	llcancel -u stud057
}
trap cleanup HUP TERM INT ABRT QUIT 

while ! llq -x | grep -q 'no job' ; do
	llq -x
	sleep 5
done
