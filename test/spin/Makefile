all: tsp rip1 rip2 oddeven lynch peterson3

%: %.pml Makefile
	spin -a $< && $(CC) -O3 -DSAFETY -DNOFAIR -DNOBOUNDCHECK -DNOVSZ pan.c -o $@
