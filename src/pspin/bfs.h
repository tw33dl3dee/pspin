/**
 * @file   bfs.h
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Sat Feb 20 23:13:22 2010
 * 
 * @brief  BFS (breadth-first search) queue operations.
 * 
 */

#ifndef _BFS_H_
#define _BFS_H_

/**
 * Size of BFS queue (in states)
 */
#define BFS_SIZE 1024

/**
 * BFS queue
 */
static struct  State** bfs_queue = NULL;
/**
 * Pointer to next element after queue top
 */
static struct State** bfs_top = NULL;

#define BFS_INIT()												\
	{															\
		bfs_queue = malloc(sizeof(struct State *)*BFS_SIZE);	\
		bfs_top = bfs_queue;									\
	}

#define BFS_ADD(state)							\
	(*bfs_top++ = state)						\
	
#define BFS_TAKE()									\
	((bfs_top == bfs_queue) ? NULL : *--bfs_top)

#endif /* _BFS_H_ */
