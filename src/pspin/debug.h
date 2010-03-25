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
 * Also, for MPI programs, MPI macro needs to be defined.
 * 
 */

/*
 * Each of the following macros, when defined, defines also generic DEBUG macro 
 * and accompaniying Xxx_dprintf() macro.
 */

#ifdef MPI_DEBUG
#	define mpi_dprintf dprintf
#	undef  DEBUG
#	define DEBUG
#else
#	define mpi_dprintf (void)
#endif

#ifdef STATE_DEBUG
#	define state_dprintf dprintf
#	define dump_dprintf  dprintf
#	undef  DEBUG
#	define DEBUG
#else
#	define state_dprintf (void)
#	define dump_dprintf  (void)
#endif


#ifdef DEBUG
#	ifdef MPI
extern int debug_node;
void debug_logger();
void dprintf(const char *format, ...) __attribute__((format (printf, 1, 2)));
void dprintf_ob(int do_buffering);
#	else
#		define dprintf printf
#		define dprintf_ob (void)
#	endif
#endif
