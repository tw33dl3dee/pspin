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

struct State** bfs_queue = NULL;
struct State** bfs_top = NULL;
