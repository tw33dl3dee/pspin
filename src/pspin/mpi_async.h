/**
 * @file   mpi_async.h
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Sat Mar 13 23:51:50 2010
 * 
 * @brief  Работа с асинхронной очередью MPI.
 * 
 */

#ifndef _MPI_ASYNC_H_
#define _MPI_ASYNC_H_

#include <mpi.h>
#include <stdint.h>

/**
 * Описатель асинхронной очереди
 */
struct mpi_queue {
	/**
	 * Массив MPI-дескрипторов запрсов
	 */
	MPI_Request *req;
	/**
	 * Массив MPI-статусов запрсов
	 */
	MPI_Status *status;
	/**
	 * Буфера для хранения запросов
	 */
	void *buf;
	/**
	 * Размер кажого буфера в байтах
	 */
	int bufsize;
	/**
	 * Чисто неиспользованных буферов (не участвующих в асинхронных MPI-операциях)
	 */
	int nfree;
	/**
	 * Общее число буферов
	 */
	int ntotal;
	/**
	 * Суммарное время ожидания завершения операций
	 */
	double wait_time;
	/**
	 * Число отправленных запросов
	 */
	int64_t n_alloc;
	/**
	 * Число освобожденных (выполненных запросов)
	 */
	int64_t n_complete;
};

/** 
 * @brief Преобразует индекс буфера в указатель на данные
 * 
 * @param queue Асинхронная очередь
 * @param bufno Индекс буфераа
 * @param type  Тип данных в буфере
 * 
 * @return Указатель на буфер (типа type *)
 */
#define MPI_ASYNC_BUF(queue, bufno, type)				\
	(type *)((queue)->buf + (queue)->bufsize*(bufno))

/** 
 * @brief Преобразует индекс буфера в указатель на его MPI-статус
 * 
 * @param queue Асинхронная очередь
 * @param bufno Индекс буфераа
 * 
 * @return Указатель на MPI_Status (определен только тогда, когда буфер был возвращен вызовом by deque_buf
 *                                 и еще не освобожден вызовом put_buf).
 */
#define MPI_ASYNC_STATUS(queue, bufno)			\
	&((queue)->status[bufno])

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
