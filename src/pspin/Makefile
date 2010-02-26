CFLAGS=-std=c99 -g -O0 -DCODEGEN_FILE=\"pan.c\" -DNODECOUNT=4 -DDEBUG -DSTATE_PARTITION_HASH -USTATE_PARTITION_FIRST_PROC 

all: state

*.o: *.h pan.c

state: state.o state_hash.o paremu.o
