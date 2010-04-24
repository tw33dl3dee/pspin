/**
 * @file   bfs_questate.h
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Sat Apr 24 14:55:06 2010
 * 
 * @brief  BFS queue operations for bitstate/hashcompact search.
 * 
 * Only states on queue are stored, after adding to hash the memory is reused.
 * 
 * New states are pushed at BFS top. Before being processed a state is copied
 * to the end of free space area, overwriting previous content, and top is decremented.
 * 
 * BFS queue ...  | ... free space ... | current state <- BFS ceil
 *                V                    V
 *            BFS top               BFS current
 *
 * After each state, it's size is stored again (so that reverse queue works as stack).
 * 
 */

#ifndef _BFS_QUESTATE_H_
#define _BFS_QUESTATE_H_

/**
 * Pointer to current state at the end of free area
 */
extern void *bfs_current;

/** 
 * @brief Initializes statespace and BFS queue
 *
 * On error, returns from current function.
 */
#define BFS_INIT()														\
	({																	\
		statespace = calloc(1, BFS_QUEUE_SIZE);							\
		if (statespace == NULL) {										\
			printf("FAILED TO ALLOC %d BYTES QUEUE SPACE\n", BFS_QUEUE_SIZE); \
			return;														\
		}																\
		if (state_hash_init() < 0)										\
			return;														\
		bfs_top = statespace;											\
		bfs_current = bfs_ceil = bfs_top + STATESPACE_SIZE;				\
	})

/** 
 * @brief Allocates new state on BFS queue
 * 
 * After allocation a state, it's either fixated by BFS_ADD()
 * or thrown away (and it's memory reused) by subsequent BFS_ALLOC().
 *
 * @param size Size of new state
 * 
 * @return Pointer to allocated state
 */
#define BFS_ALLOC(size)													\
	((bfs_top + size + STATESIZE_SIZE > bfs_current) ? NULL : bfs_top)

/** 
 * @brief Advances BFS top by the size of state on top of it
 * 
 * @param state State on top of BFS. It's memory must have been first
 *              first allocated by BFS_ALLOC().
 * 
 * @return 
 */
#define BFS_ADD(state)									\
	({													\
		++bfs_len;										\
		bfs_top += STATESIZE(state);					\
		*(STATESIZE_TYPE *)bfs_top = STATESIZE(state);	\
		bfs_top += STATESIZE_SIZE;						\
	})

/** 
 * @brief Dequeues state from BFS
 * 
 * @return Pointer to state that was next in BFS queue (NULL if queue is empty)
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
 * @brief BFS queue length (number of states queued)
 */
#define BFS_CUR_LEN()							\
	bfs_len


#endif /* _BFS_QUESTATE_H_ */
