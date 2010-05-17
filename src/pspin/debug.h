/**
 * @file   debug.h
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Sun Mar 21 17:08:48 2010
 * 
 * @brief  Макросы для отладочного журналирования.
 *
 * Для влючения журналирования отдельных частей программы нужно определить 
 * один или несколько из следующим макросов:
 * 
 *  - [MPI_DEBUG]   - операции MPI
 *  - [STATE_DEBUG] - генерация состояний
 *  - [HASH_DEBUG]  - работа с хэш-таблицей
 *
 * Журналирование также должно быть разрешено глобально макросом DEBUG.
 *
 * Для MPI-версии должен быть определен макрос MPI.
 * 
 */

/*
 * Каждый из следующих макросов, если определен, определяет соответствующие  
 * макросы Xxx_dprintf() для отладочного журналирования.
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
/*
 * God-damned xlc v6 compatibility
 */
#		define iprintf(fmt, ...) printf("[%d] " fmt, node_id, __VA_ARGS__)
#	else
#		define iprintf printf
#	endif
#endif
