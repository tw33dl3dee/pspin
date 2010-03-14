/*
 *  "Hello World" Type MPI Test Program
 */

#include <mpi.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <time.h>

#include "../../src/pspin/mpi_async.h"
#include "../../src/pspin/mpi_async.c"

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
	printf("[%lf] work time: %.1f sec\n",
		   MPI_Wtime(), worktime*1.f/CLOCKS_PER_SEC);
}

int main(int argc, char *argv[])
{
	int numprocs, myid;
	struct mpi_queue mq1, mq2;
	int bufn;
	short *buf;
	double start;
	
	MPI_Init(&argc, &argv);
	MPI_Comm_size(MPI_COMM_WORLD, &numprocs);
	MPI_Comm_rank(MPI_COMM_WORLD, &myid);

	srand(time(NULL));

	start = MPI_Wtime();
 
	mpi_async_send_start(&mq1, QLEN, BUFSIZE);
	mpi_async_recv_start(&mq2, QLEN, BUFSIZE);
	for (int i = 0; i < QLEN; ++i)
		mpi_async_put_buf(&mq2, i, BUFSIZE, MPI_CHAR, MPI_ANY_SOURCE, TAG);

	for (int i = 0; i < MAXREQ; ++i) {
		short data = 0;

		if (i || myid) {
			bufn = mpi_async_deque_buf(&mq2);
			buf = MPI_ASYNC_BUF(&mq2, bufn, short);
			//printf("[%lf] %d   recv %d-%d\n", MPI_Wtime(), myid, (int)buf[0], (int)buf[1]);
			data = buf[1]; work();
			mpi_async_put_buf(&mq2, bufn, BUFSIZE, MPI_CHAR, MPI_ANY_SOURCE, TAG);
		}

		for (int peer = 0; peer < numprocs; ++peer) {
			if (peer == myid) continue;
			bufn = mpi_async_get_buf(&mq1);
			//printf("got buffer %d\n", bufn);
			buf = MPI_ASYNC_BUF(&mq1, bufn, short);
			buf[0] = myid; buf[1] = data + 1;
			//printf("[%lf] send     %d-%d to %d\n", MPI_Wtime(), (int) buf[0], (int) buf[1], peer);
			mpi_async_queue_buf(&mq1, bufn, BUFSIZE, MPI_CHAR, peer, TAG);
		}
	}

	mpi_async_stop(&mq1);
	mpi_async_stop(&mq2);

	workstat();

	printf("[%lf] wall time: %.1f sec\n",
		   MPI_Wtime(), (float)(MPI_Wtime() - start));
 
	MPI_Finalize();
	return 0;
}
