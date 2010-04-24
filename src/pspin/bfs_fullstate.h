/**
 * @file   bfs_fullstate.h
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Tue Apr 20 00:43:49 2010
 * 
 * @brief  BFS queue operations for fullstate search.
 *
 * Statespace stores both visited states and BFS queue.
 * 
 * visited states  ... | ... BFS queue ...  | ... free space <- BFS ceil
 *                     V                    V
 *                 BFS bottom            BFS top
 *
 */

#ifndef _BFS_FULLSTATE_H_
#define _BFS_FULLSTATE_H_

/**
 * Memory for storing states.
 */
extern void *statespace;
/**
 * Pointer to the first queued (not visited yet) state.
 */
extern void *bfs_bottom;
/**
 * Pointer to the beginning of free space after BFS queue.
 */
extern void *bfs_top;
/**
 * Pointer to the end of free space.
 */
extern void *bfs_ceil;
/**
 * Number of states currently in BFS queue.
 */
extern int bfs_len;

#define BFS_INIT()														\
	({																	\
		statespace = calloc(1, STATESPACE_SIZE);						\
		if (statespace == NULL) {										\
			printf("FAILED TO ALLOC %d BYTES STATESPACE\n", STATESPACE_SIZE); \
			return;														\
		}																\
		if (state_hash_init() < 0)										\
			return;														\
		bfs_top = bfs_bottom = statespace;								\
		bfs_ceil = bfs_top + STATESPACE_SIZE;							\
	})

#define BFS_ALLOC(size)								\
	((bfs_top + size > bfs_ceil) ? NULL : bfs_top)

#define BFS_ADD(state)							\
	({											\
		++bfs_len;								\
		bfs_top += STATESIZE(state);			\
	})

#define BFS_TAKE()								\
	(BFS_CUR_LEN() ?							\
	 ({											\
		 struct State *bottom = bfs_bottom;		\
		 bfs_bottom += STATESIZE(bottom);		\
		 --bfs_len;								\
		 bottom;								\
	 })											\
	 : NULL)

#define BFS_CUR_LEN()							\
	bfs_len

#endif /* _BFS_FULLSTATE_H_ */
