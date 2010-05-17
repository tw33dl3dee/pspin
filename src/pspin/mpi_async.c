/**
 * @file   mpi_async.c
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Sat Mar 13 23:52:18 2010
 * 
 * @brief  Работа с асинхронной очередью MPI.
 * 
 */

#include <stdlib.h>
#include <assert.h>
#include <stdio.h>

#include "config.h"
#include "mpi_async.h"
#include "debug.h"

/** 
 * @brief Инициализирует асинхронную очередь
 * 
 * @param queue Указатель на очередь
 * @param queuelen Максимальная длина очереди
 * @param bufsize Максимальный размер буфера данных в операциях с очередью
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
	queue->wait_time = 0;
}

/** 
 * @brief Инициализирует асинхронную очередь отправки
 * 
 * @param queue Указатель на очередь
 * @param queuelen Максимальная длина очереди
 * @param bufsize Максимальный размер буфера данных в операциях с очередью
 */
void mpi_async_send_start(struct mpi_queue *queue, int queuelen, int bufsize)
{
	return mpi_async_init(queue, queuelen, bufsize);
}

/** 
 * @brief Выбирает следующий свободный буфер для отправки.
 * 
 * @param queue Асинхронная очередь
 * @param nowait Если != 0, не ожидать в случае отсутсвия свободных буферов.
 * 
 * @return Индекс буфера либо -1 в случае отсутствия свободных буферов при nowait != 0
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
		double start_time = MPI_Wtime();
		MPI_Waitany(queue->ntotal, queue->req, &idx, MPI_STATUS_IGNORE);
		queue->wait_time += (MPI_Wtime() - start_time);
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
 * @brief Возвращает буфер в очередь и начинает асинхронную отправку.
 * 
 * @param queue Асинхронная очередь
 * @param bufno Индекс буфера (возвращенный прежде mpi_async_get_buf())
 * @param dest MPI-назначние
 * @param tag MPI-метка
 * @param count Число элементов в буфере
 * @param type Тип элементов (MPI-тип)
 * 
 * @return Код ошибки MPI
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
 * @brief Инициализирует асинхронную очередь для приема
 * 
 * @param queue Указатель на очередь
 * @param queuelen Максимальная длина очереди
 * @param bufsize Максимальный размер буфера данных в операциях с очередью
 */
void mpi_async_recv_start(struct mpi_queue *queue, int queuelen, int bufsize)
{
	return mpi_async_init(queue, queuelen, bufsize);
}

/** 
 * @brief Выбирает из очереди следующий принятый буфер (может ожидать доставки)
 * 
 * @param queue Асинхронная очередь
 * @param nowait Не ожидать, если принятых буферов нет
 * 
 * @return Индекс буфера либо -1, если nowait != 0 и принятых буферов нет.
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
	else {
		double start_time = MPI_Wtime();
		MPI_Waitany(queue->ntotal, queue->req, &idx, &status);
		queue->wait_time += (MPI_Wtime() - start_time);
	}
	
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
 * @brief Возвращает буфер в очередь приема (начиная асинхронный прием следующего сообщения)
 * 
 * @param queue Асинхронная очередь
 * @param bufno Индекс буфер (ранее возвращенный mpi_async_deque_buf())
 * @param dest MPI-источник
 * @param tag MPI-метка
 * @param count Число элементов в буфере
 * @param type Тип элементов (MPI-тип)
 * 
 * @return Код ошибки MPI
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
 * @brief Отменяет все незаконченные операции с очередью и освобождает ресурсы.
 * 
 * @param queue Асинхронная очередь
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
