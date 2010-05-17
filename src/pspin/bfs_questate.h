/**
 * @file   bfs_questate.h
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Sat Apr 24 14:55:06 2010
 * 
 * @brief  Работа с очередью поиска в ширину при битовом хэшировании.
 * 
 * Хранятся лишь состояния в очереди, после Их обработки и добавлениия в хэш память используется повторно.
 * 
 * Новые состояния добавляются к верхушке очереди. Перед обработкой состояние переносится
 * в конец свободного пространства, перезаписывая предыдущее, и указатель на верхушку сдвигается вниз.
 * 
 * очередь ...  | ... свободное пространство ... | текущее состояние <- BFS ceil
 *             V                                V
 *          BFS top                          BFS current
 *
 * После каждого состояния в очереди хранится его размер (чтобы с ней можно было работать, как со стеком).
 * 
 */

#ifndef _BFS_QUESTATE_H_
#define _BFS_QUESTATE_H_

/**
 * Указатель на текущее состояние в конце свободной области.
 */
extern void *bfs_current;

/** 
 * @brief Инициализация пространства состояний и очереди.
 *
 * В случае ощибки, возвращает управление из текущей функции.
 */
#define BFS_INIT()														\
	({																	\
		statespace = calloc(1, BFS_QUEUE_SIZE);							\
		if (statespace == NULL) {										\
			printf("FAILED TO ALLOC %ld BYTES QUEUE SPACE\n", BFS_QUEUE_SIZE); \
			return;														\
		}																\
		if (state_hash_init() < 0)										\
			return;														\
		bfs_top = statespace;											\
		bfs_current = bfs_ceil = bfs_top + BFS_QUEUE_SIZE;				\
	})

/** 
 * @brief Выделяеет новое состояние в очереди.
 * 
 * После выделения, состояние либо фиксируется (вызовом BFS_ADD())
 * либо затирается (и его память используется вторично) следующим вызовом BFS_ALLOC().
 * 
 * @param size Размер состояния
 * 
 * @return Указатель на новое состояние
 */
#define BFS_ALLOC(size)													\
	((bfs_top + size + STATESIZE_SIZE > bfs_current) ? NULL : bfs_top)

/** 
 * @brief Продвигает указатель на верх очереди на размер состояния наверху.
 * 
 * @param state Состояние на верхушке очереди. Должно быть предварительно
 *              выделено вызовом BFS_ALLOC().
 */
#define BFS_ADD(state)									\
	({													\
		struct State *st = (state);						\
		++bfs_len;										\
		bfs_top += STATESIZE(st);						\
		*(STATESIZE_TYPE *)bfs_top = STATESIZE(st);		\
		bfs_top += STATESIZE_SIZE;						\
	})

/** 
 * @brief Выбирает следующее состояние из очереди.
 * 
 * @return Указатель на следующее состояние (NULL, если очередь пуста)
 */
#define BFS_TAKE()										\
	(BFS_CUR_LEN() ?									\
	 ({													\
		 bfs_top -= STATESIZE_SIZE;						\
		 bfs_top -= *(STATESIZE_TYPE *)bfs_top;			\
		 bfs_current = bfs_ceil - STATESIZE(bfs_top);	\
		 COPY_STATE(bfs_current, bfs_top);				\
		 --bfs_len;										\
		 (struct State *)bfs_current;					\
	 })													\
	 : NULL)

/** 
 * @brief Текущая длина очереди (количество состояний в ней)
 */
#define BFS_CUR_LEN()							\
	bfs_len

/** 
 * @brief Текущий размер очереди (суммарный размер состояний в ней в байтах)
 */
#define BFS_CUR_SIZE()									\
	((bfs_top - statespace) + (bfs_ceil - bfs_current))


#endif /* _BFS_QUESTATE_H_ */
