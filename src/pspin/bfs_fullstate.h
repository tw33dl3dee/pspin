/**
 * @file   bfs_fullstate.h
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Tue Apr 20 00:43:49 2010
 * 
 * @brief  BFS queue operations for fullstate search.
 *
 * Statespace stores both visited states and BFS queue.
 * 
 * New states are pushed at BFS top. As they are processed and become visited, 
 * BFS bottom is advanced.
 * 
 * visited states  ... | ... BFS queue ...  | ... free space <- BFS ceil
 *                     V                    V
 *                 BFS bottom            BFS top
 *
 */

#ifndef _BFS_FULLSTATE_H_
#define _BFS_FULLSTATE_H_

/**
 * Pointer to the first queued (not visited yet) state.
 */
extern void *bfs_bottom;

/** 
 * @brief Initializes statespace and BFS queue
 *
 * On error, returns from current function.
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
 * @brief Allocates new state on BFS queue
 * 
 * After allocation a state, it's either fixated by BFS_ADD()
 * or thrown away (and it's memory reused) by subsequent BFS_ALLOC().
 * 
 * @param size Size of new state
 * 
 * @return Pointer to allocated state
 */
#define BFS_ALLOC(size)							\
	((bfs_top + size > bfs_ceil) ? NULL : bfs_top)

/** 
 * @brief Advances BFS top by the size of state on top of it
 * 
 * @param state State on top of BFS. It's memory must have been first
 *              first allocated by BFS_ALLOC().
 */
#define BFS_ADD(state)							\
	({											\
		++bfs_len;								\
		bfs_top += STATESIZE(state);			\
	})

/** 
 * @brief Dequeues state from BFS
 * 
 * @return Pointer to state that was next in BFS queue (NULL if queue is empty)
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
 * @brief BFS queue length (number of states queued)
 */
#define BFS_CUR_LEN()							\
	bfs_len

#endif /* _BFS_FULLSTATE_H_ */
