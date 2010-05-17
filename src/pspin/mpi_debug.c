/**
 * @file   mpi_debug.c
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Thu Mar 25 07:53:53 2010
 * 
 * @brief  Отладочное журналирование для MPI.
 * 
 */

#include <stdarg.h>
#include <stdio.h>
#include <assert.h>
#include <mpi.h>

#include "config.h"
#include "debug.h"
#include "mpi_tags.h"

#ifdef DEBUG

/**
 * Размер буфера печати
 */
#define DEBUG_MAX_LEN 4096

extern int node_id;
extern int node_count;

/**
 * Номер узла, на котором запущена служба журналирования
 */
int debug_node;

/**
 * Если 0, вывод не буферизуется -- отправляет сразу после вывода перевода строки.
 * В противном случае посылка откладывается.
 */
static int debug_buffer_output;
/**
 * Текущая позиция выводв в буфере.
 */
static int debug_output_pos;
/**
 * Буфер с отладочным выводом текущего узла
 */
static char debug_output[DEBUG_MAX_LEN];

/** 
 * @brief Служба журналирования
 *
 * Принимает сообщения с отладочным выводом и выводит их
 */
void debug_logger() 
{
	MPI_Status status;
	int res;
	/**
	 * Number of "terminate" messages received.
	 */
	int termination_count = 0;

	while ((res = MPI_Recv(debug_output, sizeof(debug_output), MPI_CHAR, 
						   MPI_ANY_SOURCE, MPI_ANY_TAG, MPI_COMM_WORLD, &status)) == MPI_SUCCESS) {
		switch (status.MPI_TAG) {
		case TagTerminate:
			/* Logger can terminate only after every other node has terminated.
			 * So we receive termination request from each node and exit then only.
			 */
			if (++termination_count >= node_count)
				return;
			break;

		case TagDebugLog:
			printf("[%d] %s", status.MPI_SOURCE, debug_output);
			break;

		default:
			assert(/* invalid tag */ 0);
		}
	}
}

/** 
 * @brief Отправляет текущее содержимое буфера вывода узлу журналирования
 */
static void flush_output()
{
	MPI_Send(debug_output, debug_output_pos + 1, MPI_CHAR, debug_node, TagDebugLog, MPI_COMM_WORLD);
	debug_output_pos = 0;
}

/** 
 * @brief Вывод на печать в стиле printf.
 */
void dprintf(const char *format, ...)
{
	va_list va;

	va_start(va, format);
	debug_output_pos += vsnprintf(debug_output + debug_output_pos, 
								  sizeof(debug_output) - debug_output_pos, 
								  format, va);
	if (debug_output_pos > sizeof(debug_output))
		debug_output_pos = sizeof(debug_output);
	va_end(va);

	if (debug_output[debug_output_pos - 1] == '\n' && !debug_buffer_output)
		flush_output();
}

/** 
 * @brief Включает и выключает буферизацию вывода.
 * 
 * @param do_buffering Если 0, отключает буферизацию и отправляет текущее содержимое.
 *                     В противном случае включает буферизацию.
 */
void dprintf_ob(int do_buffering)
{
	debug_buffer_output = do_buffering;
	if (!debug_buffer_output)
		flush_output();
}

#endif // DEBUG
