#!/bin/sh

for FILE in pspin.std*; do
	cat $FILE | sort -k1,1 -s > $FILE.log
	rm -f $FILE
done
