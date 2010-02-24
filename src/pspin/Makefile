CFLAGS=-std=c99 -g -O0 -DCODEGEN_FILE=\"pan.c\" -DDEBUG

all: state

*.o: *.h pan.c

state: state.o state_hash.o 
