/**
 * @file   bfs_fullstate.h
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Tue Apr 20 00:43:49 2010
 * 
 * @brief  Работа с очередью поиска в ширину при полном хранении состояний.
 *
 * Хранятся как посещенные состояния, так и находящиеся в очереди.
 * 
 * Новые состояния заталкиваются в очередь с верхухшки. По мере того, как они
 * обрабатываются, указатель на начало очереди сдвигается.
 * 
 * посещенные состояния  ... | ... очередь поиска ...  | ... незанятое пространство <- BFS ceil
 *                           V                         V
 *                       BFS bottom                 BFS top
 *
 */

#ifndef _BFS_FULLSTATE_H_
#define _BFS_FULLSTATE_H_

/**
 * Указатель на начало очереди.
 */
extern void *bfs_bottom;

/** 
 * @brief Инициализация пространства состояний и очереди.
 *
 * В случае ощибки, возвращает управление из текущей функции.
 */
#define BFS_INIT()														\
	({																	\
		statespace = calloc(1, STATESPACE_SIZE);						\
		if (statespace == NULL) {										\
			printf("FAILED TO ALLOC %ld BYTES STATESPACE\n", STATESPACE_SIZE); \
			return;														\
		}																\
		if (state_hash_init() < 0)										\
			return;														\
		bfs_top = bfs_bottom = statespace;								\
		bfs_ceil = bfs_top + STATESPACE_SIZE;							\
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
#define BFS_ALLOC(size)							\
	((bfs_top + size > bfs_ceil) ? NULL : bfs_top)

/** 
 * @brief Продвигает указатель на верх очереди на размер состояния наверху.
 * 
 * @param state Состояние на верхушке очереди. Должно быть предварительно
 *              выделено вызовом BFS_ALLOC().
 */
#define BFS_ADD(state)							\
	({											\
		++bfs_len;								\
		bfs_top += STATESIZE(state);			\
	})

/** 
 * @brief Выбирает следующее состояние из очереди.
 * 
 * @return Указатель на следующее состояние (NULL, если очередь пуста)
 */
#define BFS_TAKE()								\
	(BFS_CUR_LEN() ?							\
	 ({											\
		 struct State *bottom = bfs_bottom;		\
		 bfs_bottom += STATESIZE(bottom);		\
		 --bfs_len;								\
		 bottom;								\
	 })											\
	 : NULL)

/** 
 * @brief Текущая длина очереди (количество состояний в ней)
 */
#define BFS_CUR_LEN()							\
	bfs_len

#endif /* _BFS_FULLSTATE_H_ */
