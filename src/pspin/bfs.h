/**
 * @file   bfs.h
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Sat Feb 20 23:13:22 2010
 * 
 * @brief  Работа с очередью поиска в ширину.
 * 
 */

#ifndef _BFS_H_
#define _BFS_H_

#include "config.h"

#include "state.h"
#include "state_hash.h"

/**
 * Область памяти для хранения состояний.
 */
extern void *statespace;
/**
 * Число состояний в очереди в данный момент.
 */
extern size_t bfs_len;
/**
 * Указатель на начало незанятого пространства..
 */
extern void *bfs_top;
/**
 * Указатель на конец незанятого пространства.
 */
extern void *bfs_ceil;

#ifdef FULLSTATE 
#	include "bfs_fullstate.h"
#else
#	include "bfs_questate.h"
#endif

#endif /* _BFS_H_ */
