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

#include "config.h"

#include "state.h"
#include "state_hash.h"

/**
 * Memory for storing states.
 */
extern void *statespace;
/**
 * Number of states currently in BFS queue.
 */
extern int bfs_len;
/**
 * Pointer to the beginning of free space after BFS queue.
 */
extern void *bfs_top;
/**
 * Pointer to the end of free space.
 */
extern void *bfs_ceil;

#ifdef FULLSTATE 
#	include "bfs_fullstate.h"
#else
#	include "bfs_nostate.h"
#endif

#endif /* _BFS_H_ */
