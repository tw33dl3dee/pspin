/**
 * @file   debug.h
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Sun Mar 21 17:08:48 2010
 * 
 * @brief  Debug logging macros.
 * 
 */

/**
 * If 1, turn on MPI debug logging.
 */
#define MPI_DEBUG 1
/**
 * If 1, turn on statespace debug logging.
 */
#define STATE_DEBUG 1

#if MPI_DEBUG == 1
#	define mpi_dprintf printf
#else
#	define mpi_dprintf (void)
#endif

#if STATE_DEBUG == 1
#	define state_dprintf printf
#else
#	define state_dprintf (void)
#endif
