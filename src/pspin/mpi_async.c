/**
 * @file   mpi_async.c
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Sat Mar 13 23:52:18 2010
 * 
 * @brief  MPI mpi_async queueing facilities.
 * 
 */

#include <stdlib.h>
#include <assert.h>
#include <stdio.h>

#include "config.h"
#include "mpi_async.h"
#include "debug.h"

/** 
 * @brief Initializes async MPI queue for reception or delivery
 * 
 * @param queue Queue to initialize
 * @param queuelen Maximum queue lenth
 * @param bufsize Maximum size of data buffer that will be used
 */
void mpi_async_init(struct mpi_queue *queue, int queuelen, int bufsize)
{
	queue->bufsize = bufsize;
	queue->buf	  = malloc(queuelen * bufsize);
	queue->req	  = malloc(queuelen * sizeof(MPI_Request));
	queue->status = malloc(queuelen * sizeof(MPI_Status));
	for (int i = 0; i < queuelen; ++i)
		queue->req[i] = MPI_REQUEST_NULL;
	queue->nfree = queuelen;
	queue->ntotal = queuelen;
}

/** 
 * @brief Initializes async MPI queue for sending messages
 * 
 * @param queue Queue to initialize
 * @param queuelen Maximum queue length
 * @param bufsize Maximum size of data buffer that will be used
 */
void mpi_async_send_start(struct mpi_queue *queue, int queuelen, int bufsize)
{
	mpi_async_init(queue, queuelen, bufsize);
}

/** 
 * @brief Takes unused buffer from sending queue
 * 
 * @param queue Async queue (must be initialized)
 * @param nowait Return immediately, never wait
 * 
 * @return Buffer index (or -1 if no buffers available and nowait != 0)
 * @sa MPI_ASYNC_BUF
 */
int mpi_async_get_buf(struct mpi_queue *queue, int nowait)
{
	mpi_dprintf("[free buffers left: %d] ", queue->nfree);
	if (queue->nfree > 0) {
		queue->nfree--;
		for (int i = 0; i < queue->ntotal; ++i)
			if (queue->req[i] == MPI_REQUEST_NULL)
				return i;
		assert(/* queue->nfree == 0 */ 0);
	}
	else if (!nowait) {
		int firstidx, idx, flag = 1;
		MPI_Waitany(queue->ntotal, queue->req, &idx, MPI_STATUS_IGNORE);
		firstidx = idx;
		assert(idx != MPI_UNDEFINED);
		for (flag = 1; flag && idx != MPI_UNDEFINED; 
			 MPI_Testany(queue->ntotal, queue->req, &idx, &flag, MPI_STATUS_IGNORE)) {
			queue->req[idx] = MPI_REQUEST_NULL;
			queue->nfree++;
		}
		queue->nfree--;
		mpi_dprintf("[wait idx: %d, free buffers: %d] ", firstidx, queue->nfree);
		return firstidx;
	}
	else
		return -1;
}

/** 
 * @brief Queues previously taken buffer for delivery
 * 
 * @param queue Async queue (must be initialized)
 * @param bufno Buffer index (as returned by mpi_async_get_buf())
 * @param dest MPI destination
 * @param tag MPI tag
 * @param count Element count
 * @param type Element MPI type
 * 
 * @return Error status
 * @sa MPI_Send
 */
int mpi_async_queue_buf(struct mpi_queue *queue, int bufno, 
						int count, MPI_Datatype type, int dest, int tag)
{
	return MPI_Isend(MPI_ASYNC_BUF(queue, bufno, void), 
					 count, type, dest, tag, 
					 MPI_COMM_WORLD, queue->req + bufno);
}

/** 
 * @brief Initializes async MPI queue for receiving messages
 * 
 * @param queue Queue to initialize
 * @param queuelen Maximum queue length
 * @param bufsize Maximum size of data buffer that will be used
 */
void mpi_async_recv_start(struct mpi_queue *queue, int queuelen, int bufsize)
{
	mpi_async_init(queue, queuelen, bufsize);
}

/** 
 * @brief Deques buffer (waits for any receive operation to complete)
 * 
 * @param queue Async queue (must be initialized)
 * @param nowait Return immediately, never wait
 * 
 * @return Buffer index (or -1, if no receive operations have been completed
 *                       and nowait != 0)
 *
 * @sa MPI_ASYNC_BUF
 */
int mpi_async_deque_buf(struct mpi_queue *queue, int nowait)
{
	int idx, flag;
	MPI_Status status;

	if (nowait) {
		MPI_Testany(queue->ntotal, queue->req, &idx, &flag, &status);
		if (!flag)
			return -1;
	}
	else
		MPI_Waitany(queue->ntotal, queue->req, &idx, &status);
	
	/* Should be at least one recv operation in progress
	 */
	assert(idx != MPI_UNDEFINED);
	/* We count unused requests for debugging purposes only
	 */
	assert(++queue->nfree);
	queue->status[idx] = status;
	queue->req[idx] = MPI_REQUEST_NULL;
	return idx;
}

/** 
 * @brief Puts buffer into receive queue (starting async receive on it)
 * 
 * @param queue Async queue (must be initialized)
 * @param bufno Buffer index (0 .. queue length - 1)
 * @param dest MPI source
 * @param tag MPI tag
 * @param count Element count
 * @param type Element MPI type
 * 
 * @return Error status
 * @sa MPI_Recv
 */
int mpi_async_put_buf(struct mpi_queue *queue, int bufno, 
					  int count, MPI_Datatype type, int src, int tag)
{
	assert(--queue->nfree >= 0);
	return MPI_Irecv(MPI_ASYNC_BUF(queue, bufno, void), 
					 count, type, src, tag, 
					 MPI_COMM_WORLD, queue->req + bufno);
}

/** 
 * @brief Cancels all async operations on queue and frees it's memory
 * 
 * @param queue Async queue (must be initialized)
 */
void mpi_async_stop(struct mpi_queue *queue)
{
	for (int i = 0; i < queue->ntotal; ++i)
		if (queue->req[i] != MPI_REQUEST_NULL) {
			MPI_Cancel(&queue->req[i]);
			MPI_Wait(&queue->req[i], MPI_STATUS_IGNORE);
		}
	free(queue->buf);
	free(queue->req);
}
