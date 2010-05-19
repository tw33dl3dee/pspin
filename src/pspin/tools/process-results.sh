#!/bin/sh

mv pspin.*stderr pspin.stderr
mv pspin.*stdout pspin.stdout 

for FILE in pspin.stdout pspin.stderr; do
	[ -e $FILE ] && cat $FILE | sort -k1,2 -s | grep -v PROGRESS > $FILE.log
	rm -f $FILE
done

cat pspin.stderr.log | grep -v indirect_max_size 2>/dev/null
