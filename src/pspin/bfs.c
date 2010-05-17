/**
 * @file   bfs.c
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Wed Mar 10 21:28:13 2010
 * 
 * @brief  Работа с очередью поиска в ширину.
 * 
 * Файл содержит только объявления глобальных переменных, 
 * функционал вынесен в заголовочные файлы.
 */

#include <stdlib.h>

#include "config.h"
#include "bfs.h"

void *statespace = NULL;
void *bfs_top = NULL;
void *bfs_ceil = NULL;
size_t bfs_len = 0;

#ifdef FULLSTATE
void *bfs_bottom = NULL;
#else
void *bfs_current = NULL;
#endif
