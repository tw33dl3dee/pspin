/**
 * @file   mpi_debug.c
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Thu Mar 25 07:53:53 2010
 * 
 * @brief  MPI debug logger process and utils.
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
 * Length of debug output buffer
 */
#define DEBUG_MAX_LEN 4096

extern int node_id;
extern int node_count;

/**
 * Node number which is receives debugging messages
 */
int debug_node;

/**
 * If 0, don't buffer any output -- send it as soon as newline is printed.
 * Otherwise, defer actual sending to debug node
 */
static int debug_buffer_output;
/**
 * Current position in debug ouput buffer to append to
 */
static int debug_output_pos;
/**
 * Buffer with debug output of current node
 */
static char debug_output[DEBUG_MAX_LEN];

/** 
 * @brief Debug logging daemon
 *
 * Receives debug messages and prints them.
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
 * @brief Sends current contents of debug output buffer to debug logging node.
 */
static void flush_output()
{
	MPI_Send(debug_output, debug_output_pos + 1, MPI_CHAR, debug_node, TagDebugLog, MPI_COMM_WORLD);
	debug_output_pos = 0;
}

/** 
 * @brief printf-like MPI debug printer.
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
 * @brief Turns output buffering on and off.
 * 
 * @param do_buffering If 0, turns buffering off and sends current buffer content.
 *                     Otherwise, turns it on.
 */
void dprintf_ob(int do_buffering)
{
	debug_buffer_output = do_buffering;
	if (!debug_buffer_output)
		flush_output();
}

#endif // DEBUG
