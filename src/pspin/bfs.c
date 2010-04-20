/**
 * @file   bfs.c
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Wed Mar 10 21:28:13 2010
 * 
 * @brief  BFS (breadth-first search) queue operations.
 * 
 */

#include <stdlib.h>

#include "config.h"
#include "bfs.h"

#ifdef FULLSTATE

void *statespace = NULL;
void *bfs_bottom = NULL;	// struct State *
void *bfs_top = NULL;		// struct State *
void *bfs_ceil = NULL;
int bfs_len = 0;

#endif
