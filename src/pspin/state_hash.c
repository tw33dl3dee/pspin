/**
 * @file   state_hash.c
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Mon Feb 22 20:21:46 2010
 * 
 * @brief  Hashing functions and hashtable implementation.
 * 
 */

#include <stdlib.h>
#include <stdio.h>

#include "state.h"
#include "state_hash.h"

/**
 * State bit-hashtable
 */
static char state_hashtable[HASH_SIZE/8];

/** 
 * @brief Lookups state and hash table, adding new if none was found.
 * 
 * @param state state structure
 * 
 * @return 1 if new state was added, 0 if it was present.
 */
int state_hash_add(struct State *state)
{
	state_hash_t hash = STATE_HASH(state) % HASH_SIZE;
	int old = BIT_TEST(state_hashtable, hash);
	BIT_SET(state_hashtable, hash);
	printf("State hash (%lu)", hash);
	return !old;
}
