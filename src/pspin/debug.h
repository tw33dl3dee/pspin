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
 *  - [HASH_DEBUG]  - debug hashtable operations
 *
 * Logging must be globally enabled by defining DEBUG macro.
 * If DEBUG is not defined, logging is turned off in whole program.
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

#ifdef HASH_DEBUG
#	define hash_dprintf dprintf
#else
#	define hash_dprintf (void)
#endif

#ifdef DEBUG
#	ifdef MPI
extern int debug_node;
void debug_logger();
void mpi_printf(const char *format, ...) __attribute__((format (printf, 1, 2)));
void mpi_printf_ob(int do_buffering);
#		define dprintf mpi_printf
#		define iprintf mpi_printf
#		define dprintf_ob mpi_printf_ob
#	else
#		define dprintf printf
#		define iprintf printf
#		define dprintf_ob (void)
#	endif
#else
#	define dprintf (void)
#	define dprintf_ob (void)
#	ifdef MPI
extern int node_id;
#		define iprintf(fmt, args...) printf("[%d] " fmt, node_id, ## args)
#	else
#		define iprintf printf
#	endif
#endif
