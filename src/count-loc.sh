#!/bin/bash

print_d1000() {
    WHOLE=$(($1 / 1000))
    FRACTION=$(($1 - $WHOLE * 1000))
    printf "%d.%03d" $WHOLE $FRACTION
}

print_d1024() {
    WHOLE=$(($1 / 1024))
    FRACTION=$(($1 % 1024 * 1000 / 1024))
    printf "%d.%03d" $WHOLE $FRACTION
}

stat_init() {
    echo "0 0"
}

stat_get() {
    find $1 -type f -exec file {} + | grep -E "program|script" | cut -f1 -d: | xargs wc -lc | tail -n1
}

stat_add() {
	L1=$1; B1=$2; L2=$3; B2=$4
    echo $((L1 + L2)) $((B1 + B2))
}

stat_print() {
	printf "%10s KiB (%d B)\n" $(print_d1024 $2) $2
	printf "%10s kLOC (avg line %.1f char)\n" $(print_d1000 $1) $(($2/$1))
}

loc_stat() {
    TOTAL=$(stat_init)
    for ENTRY in "$@"; do
		[[ -d "$ENTRY" ]] || continue
        STAT=$(stat_get "$ENTRY")
        echo $(readlink -mn "$ENTRY"):
        stat_print $STAT
        TOTAL=$(stat_add $TOTAL $STAT)
    done
    echo "Total:"
    stat_print $TOTAL
}

loc_stat "$@"
