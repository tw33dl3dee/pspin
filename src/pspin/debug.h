/**
 * @file   debug.h
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Sun Mar 21 17:08:48 2010
 * 
 * @brief  Debug logging macros.
 *
 * To turn on debug logging for specific parts of program, define one or more of
 * the following macros:
 * 
 *  - [MPI_DEBUG]   - debug MPI
 *  - [STATE_DEBUG] - debug statespace generation
 * 
 */

#ifdef MPI_DEBUG
#	define mpi_dprintf dprintf
#else
#	define mpi_dprintf (void)
#endif

#ifdef STATE_DEBUG
#	define state_dprintf dprintf
#	define dump_dprintf  dprintf
#else
#	define state_dprintf (void)
#	define dump_dprintf  (void)
#endif

#if defined(MPI_DEBUG)

extern int node_id, node_count;
extern int output_flushed;

#	include <mpi.h>

#	define dprintf(format, args...)										\
	({																	\
		if (output_flushed)												\
			fprintf(stdout, "%lf [%d/%d] " format,						\
					MPI_Wtime(), node_id, node_count, ## args);			\
		else															\
			fprintf(stdout, format, ## args);							\
		output_flushed = (format[sizeof(format) - 2] == '\n');			\
	})

#elif defined(STATE_DEBUG)

#	define dprintf(format, args...)				\
	fprintf(stdout, format, ## args)

#else  /* no debug output needed */

#	define dprintf(...) (void)

#endif
