/**
 * @file   mpi_async.h
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Sat Mar 13 23:51:50 2010
 * 
 * @brief  MPI async queueing facilities.
 * 
 */

#ifndef _MPI_ASYNC_H_
#define _MPI_ASYNC_H_

#include <mpi.h>

/**
 * MPI async queue
 */
struct mpi_queue {
	/**
	 * Request array
	 */
	MPI_Request *req;
	/**
	 * Status array
	 */
	MPI_Status *status;
	/**
	 * Buffers used for requests
	 */
	void *buf;
	/**
	 * Size of each buffer in bytes
	 */
	int bufsize;
	/**
	 * Number of unused (not bound by recv/send operation) buffers
	 */
	int nfree;
	/**
	 * Total number of buffers
	 */
	int ntotal;
	/**
	 * Time spent waiting for buffers
	 */
	double wait_time;
};

/** 
 * @brief Converts buffer number to buffer address
 * 
 * @param queue MPI queue
 * @param bufno Buffer number
 * @param type  Buffer datatype
 * 
 * @return Pointer to buffer (type *)
 */
#define MPI_ASYNC_BUF(queue, bufno, type)				\
	(type *)((queue)->buf + (queue)->bufsize*(bufno))

/** 
 * @brief Converts buffer number to it's MPI_Status record address
 * 
 * @param queue MPI queue
 * @param bufno Buffer number 
 * 
 * @return Pointer to MPI_Status structure (undefined unless buffer number was returned 
 *                                          by deque_buf and not reclaimed by put_buf yet).
 */
#define MPI_ASYNC_STATUS(queue, bufno)			\
	&((queue)->status[bufno])

/** 
 * @brief Checks if address is an async buffer or not
 * 
 * @param queue MPI queue
 * @param buf (Possible) buffer address
 * 
 * @return True if address points to an async buffer
 */
#define MPI_IS_ASYNC_BUF(queue, buf)									\
	((queue)->buf <= (buf) &&											\
	 (buf)        <  (queue)->buf + (queue)->bufsize*(queue)->ntotal)

void mpi_async_init(struct mpi_queue *queue, int queuelen, int bufsize);
void mpi_async_send_start(struct mpi_queue *queue, int queuelen, int bufsize);
void mpi_async_recv_start(struct mpi_queue *queue, int queuelen, int size);
void mpi_async_stop(struct mpi_queue *queue);

int mpi_async_get_buf(struct mpi_queue *queue, int nowait);
int mpi_async_queue_buf(struct mpi_queue *queue, int bufno, 
						int count, MPI_Datatype type, int dest, int tag);

int mpi_async_deque_buf(struct mpi_queue *queue, int nowait);
int mpi_async_put_buf(struct mpi_queue *queue, int bufno, 
					  int count, MPI_Datatype type, int src, int tag);

#endif /* _MPI_ASYNC_H_ */
