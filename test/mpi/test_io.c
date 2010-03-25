/*
 *  Concurrent MPI IO tests
 */

#include <mpi.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <time.h>
#include <stdlib.h>
#include <stdio.h>

#define BUFSIZE 1280
#define TAG 0
#define MAXREQ 10000
#define QLEN 16
#define WORKHARD 100000

int worktime, nwork;

void work()
{
	time_t start = clock();
	while (rand() % WORKHARD);
	worktime += (clock() - start);
	nwork++;
}

void workstat()
{
	printf("[%d] work time: %.1f sec\n",
		   getpid(), worktime*1.f/CLOCKS_PER_SEC);
}

int main(int argc, char *argv[])
{
	int numprocs, myid;
	char buf[4096];
	double start;
	MPI_File fh;
	MPI_Status status;
	int res;
	
	MPI_Init(&argc, &argv);
	MPI_Comm_size(MPI_COMM_WORLD, &numprocs);
	MPI_Comm_rank(MPI_COMM_WORLD, &myid);

	res = MPI_File_open(MPI_COMM_WORLD, "abcdef.log", MPI_MODE_RDWR | MPI_MODE_CREATE, 
						MPI_INFO_NULL, &fh);

	printf("File: %p (res %d)\n", fh, res);

	srand(time(NULL));

	start = MPI_Wtime();

	snprintf(buf, sizeof(buf), "I'm number %d\n", myid);
	MPI_File_write_shared(fh, buf, strlen(buf), MPI_CHAR, &status);

	workstat();

	printf("[%d] wall time: %.1f sec\n",
		   getpid(), (float)(MPI_Wtime() - start));
 
	MPI_File_close(&fh);
	MPI_Finalize();
	return 0;
}
