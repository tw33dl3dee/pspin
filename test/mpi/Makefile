LDFLAGS += -lmpi
CFLAGS=-std=c99 -g

all: test1 test_async test_async_many

test_async.o: ../../src/pspin/mpi_async.h ../../src/pspin/mpi_async.c
test_async_many.o: ../../src/pspin/mpi_async.h ../../src/pspin/mpi_async.c
