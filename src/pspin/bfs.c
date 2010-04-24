/**
 * @file   bfs.c
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Wed Mar 10 21:28:13 2010
 * 
 * @brief  BFS (breadth-first search) queue operations.
 * 
 * This file is solely for global data definitions, all operations
 * are defined as macros in appropriate header files.
 */

#include <stdlib.h>

#include "config.h"
#include "bfs.h"

void *statespace = NULL;
void *bfs_top = NULL;
void *bfs_ceil = NULL;
int bfs_len = 0;

#ifdef FULLSTATE
void *bfs_bottom = NULL;
#else
void *bfs_current = NULL;
#endif
