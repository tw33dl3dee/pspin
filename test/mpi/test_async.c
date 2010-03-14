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
	printf("[%d] work time: %.1f sec\n",
		   getpid(), worktime*1.f/CLOCKS_PER_SEC);
}

int main(int argc, char *argv[])
{
	int numprocs, myid;
	struct mpi_queue mq;
	int bufn;
	short *buf;
	double start;
	
	MPI_Init(&argc, &argv);
	MPI_Comm_size(MPI_COMM_WORLD, &numprocs);
	MPI_Comm_rank(MPI_COMM_WORLD, &myid);

	srand(time(NULL));

	start = MPI_Wtime();
 
	if (myid == 0) {
		mpi_async_send_start(&mq, QLEN, BUFSIZE);
		for (int i = 0; i < MAXREQ; ++i) {
			bufn = mpi_async_get_buf(&mq);
			//printf("got buffer %d\n", bufn);
			buf = MPI_ASYNC_BUF(&mq, bufn, short);
			work(); buf[0] = i;
			//printf("[%d] send     %d\n", getpid(), (int) buf[0]);
			/* Check if half-sized buffer works */
			mpi_async_queue_buf(&mq, bufn, BUFSIZE/2, MPI_CHAR, 1, TAG);
		}
		//sleep(5);
	}
	else {
		mpi_async_recv_start(&mq, QLEN, BUFSIZE);
		for (int i = 0; i < QLEN; ++i)
			mpi_async_put_buf(&mq, i, BUFSIZE, MPI_CHAR, 0, TAG);
		for (int i = 0; i < MAXREQ; ++i) {
			bufn = mpi_async_deque_buf(&mq);
			buf = MPI_ASYNC_BUF(&mq, bufn, short);
			//printf("[%d]     recv %d\n", getpid(), (int)buf[0]);
			assert(buf[0] == i);
			work();
			mpi_async_put_buf(&mq, bufn, BUFSIZE, MPI_CHAR, 0, TAG);
		}
		//sleep(5);
	}

	mpi_async_stop(&mq);

	workstat();

	printf("[%d] wall time: %.1f sec\n",
		   getpid(), (float)(MPI_Wtime() - start));
 
	MPI_Finalize();
	return 0;
}
