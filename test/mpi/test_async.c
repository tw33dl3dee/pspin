/*
 *  "Hello World" Type MPI Test Program
 */

#include <mpi.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <stdlib.h>
#include <assert.h>
#include <time.h>

struct mpi_queue {
	MPI_Request *req;
	void *buf;
	int bufsize;
	int nfree;
	int ntotal;

	MPI_Datatype mpi_type;
	int mpi_count;;
};

#define ASYNC_BUF(queue, bufno, type)			\
	(type *)((queue)->buf + (queue)->bufsize*(bufno))

void async_init(struct mpi_queue *queue, int queuelen, int bufsize, 
				int count, MPI_Datatype type)
{
	queue->bufsize = bufsize;
	queue->buf = malloc(queuelen * bufsize);
	queue->req = malloc(queuelen * sizeof(MPI_Request));
	for (int i = 0; i < queuelen; ++i)
		queue->req[i] = MPI_REQUEST_NULL;
	queue->nfree = queuelen;
	queue->ntotal = queuelen;
	queue->mpi_type = type;
	queue->mpi_count = count;
}

void async_send_start(struct mpi_queue *queue, int queuelen, int bufsize, 
					  int count, MPI_Datatype type)
{
	return async_init(queue, queuelen, bufsize, count, type);
}

int async_get_buf(struct mpi_queue *queue)
{
	//printf("free buffers left: %d\n", queue->nfree);
	queue->nfree--;
	if (queue->nfree >= 0) {
		for (int i = 0; i < queue->ntotal; ++i)
			if (queue->req[i] == MPI_REQUEST_NULL)
				return i;
	}
	else {
		int firstidx, idx, flag = 1;
		MPI_Waitany(queue->ntotal, queue->req, &idx, MPI_STATUS_IGNORE);
		firstidx = idx;
		assert(idx != MPI_UNDEFINED);
		for (flag = 1; flag && idx != MPI_UNDEFINED; 
			 MPI_Testany(queue->ntotal, queue->req, &idx, &flag, MPI_STATUS_IGNORE)) {
			queue->req[idx] = MPI_REQUEST_NULL;
			queue->nfree++;
		}
		//printf("wait idx: %d\n", firstidx);
		//printf("free bufs: %d\n", queue->nfree);
		return firstidx;
	}
}

int async_queue_buf(struct mpi_queue *queue, int bufno, 
					int dest, int tag)
{
	return MPI_Isend(ASYNC_BUF(queue, bufno, void), 
					 queue->mpi_count, queue->mpi_type, 
					 dest, tag, MPI_COMM_WORLD, 
					 queue->req + bufno);
}

void async_recv_start(struct mpi_queue *queue, int queuelen, int size,
					  int count, MPI_Datatype type)
{
	return async_init(queue, queuelen, size, count, type);
}

int async_deque_buf(struct mpi_queue *queue)
{
	int idx;
	MPI_Waitany(queue->ntotal, queue->req, &idx, MPI_STATUS_IGNORE);
	assert(idx != MPI_UNDEFINED);
	/* We count unused request for debugging purposes only
	 */
	assert(++queue->nfree);
	queue->req[idx] = MPI_REQUEST_NULL;
	return idx;
}

int async_put_buf(struct mpi_queue *queue, int bufno, 
				  int src, int tag)
{
	assert(--queue->nfree >= 0);
	return MPI_Irecv(ASYNC_BUF(queue, bufno, void), 
					 queue->mpi_count, queue->mpi_type,
					 src, tag, MPI_COMM_WORLD,
					 queue->req + bufno);
}

void async_stop(struct mpi_queue *queue)
{
}

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
		async_send_start(&mq, QLEN, BUFSIZE, BUFSIZE, MPI_CHAR);
		for (int i = 0; i < MAXREQ; ++i) {
			bufn = async_get_buf(&mq);
			//printf("got buffer %d\n", bufn);
			buf = ASYNC_BUF(&mq, bufn, short);
			work(); buf[0] = i;
			//printf("[%d] send     %d\n", getpid(), (int) buf[0]);
			async_queue_buf(&mq, bufn, 1, TAG);
		}
		//sleep(5);
	}
	else {
		async_recv_start(&mq, QLEN, BUFSIZE, BUFSIZE, MPI_CHAR);
		for (int i = 0; i < QLEN; ++i)
			async_put_buf(&mq, i, 0, TAG);
		for (int i = 0; i < MAXREQ; ++i) {
			bufn = async_deque_buf(&mq);
			buf = ASYNC_BUF(&mq, bufn, short);
			//printf("[%d]     recv %d\n", getpid(), (int)buf[0]);
			assert(buf[0] == i);
			work();
			async_put_buf(&mq, bufn, 0, TAG);
		}
		//sleep(5);
	}

	workstat();

	printf("[%d] wall time: %.1f sec\n",
		   getpid(), (float)(MPI_Wtime() - start));
 
	MPI_Finalize();
	return 0;
}
