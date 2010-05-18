#!/bin/sh

for FILE in pspin.stdout pspin.stderr; do
	[ -e $FILE ] && cat $FILE | sort -k1,1 -s | grep -v PROGRESS > $FILE.log
	rm -f $FILE
done

cat pspin.stderr.log 2>/dev/null || echo "==VERIFICATION PASSED"
