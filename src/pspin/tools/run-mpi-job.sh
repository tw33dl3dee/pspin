#!/bin/sh

JOB_NAME=pspin.job

rm -f pspin.*std*

make pspin -f Makefile.bare || exit 1

SUBMIT=$(llsubmit $JOB_NAME)

echo $SUBMIT
JOBID=$(echo $SUBMIT | grep -o 'mgmt.nodes.[0-9]*')
echo "Job ID: $JOBID"

cleanup ()  {
	llcancel -u stud057
}
trap cleanup HUP TERM INT ABRT QUIT 

while ! llq -x $JOBID | grep -q 'no job' ; do
	llq -x $JOBID
	sleep 5
done
