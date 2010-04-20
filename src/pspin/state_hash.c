/**
 * @file   state_hash.c
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Mon Feb 22 20:21:46 2010
 * 
 * @brief  Hashing functions and hashtable implementation.
 * 
 */

#include "config.h"
#include "state.h"
#include "state_hash.h"
#include "debug.h"

#ifdef FULLSTATE

/*
 * Fullstate hashing: states are fully stored and compared on hash-lookups.
 * Open addressing is used for collision resolution.
 */

/**
 * Hash table stores pointers to states stored on visited/BFS state stack
 * 
 * @sa statespace
 */
static struct State **state_hashtable;

static int used_hash_entries;
static int hash_collisions;
static int hash_collision_shifts;

/** 
 * @brief Initializes hash table, allocating memory for it.
 * 
 * @return 0 on success, -1 if allocation failed.
 */
int state_hash_init()
{
	state_hashtable = calloc(sizeof(struct State *), HASHTABLE_SIZE);
	if (state_hashtable == NULL) {
		printf("FAILED TO ALLOC %d BYTES HASHTABLE\n", HASHTABLE_SIZE);
		return -1;
	}
	return 0;
}

#define SQR(x)									\
	({ __typeof__(x) _x = (x); _x*_x; })

/** 
 * @brief Lookups state and hash table, adding new if none was found.
 * 
 * @param state state structure
 * 
 * @return 1 if new state was added, 0 if it was present.
 */
int state_hash_add(struct State *state)
{
	state_hash_t hash = STATE_HASH(state) % HASHTABLE_SIZE;
	state_hash_t offset = 0;
	struct State *st;
	int found = 0;
	int had_collisions = 0;

	hash_dprintf("State hash (" HASH_FMT ")", hash);

	for (st = state_hashtable[hash];
		 st != NULL 
			 && (STATESIZE(state) != STATESIZE(st) || 
				 memcmp(state, st, STATESIZE(state)));
		 st = state_hashtable[hash]) {
		/*
		 * Hash slot already occupied by a state address (not NULL)
		 * which is not the same as new state
		 */
		hash_dprintf(" {COLLISION IN SLOT " HASH_FMT, SQR(offset));
		++hash_collision_shifts;
		had_collisions = 1;
		/*
		 * Square open addressing: slot, slot+1, slot+4, slot+9,..
		 */
		hash += SQR(++offset);
		hash %= HASHTABLE_SIZE;
		hash_dprintf(", NEXT " HASH_FMT "}", hash);
	}

	if (had_collisions)
		hash_collisions++;

	/*
	 * If last slot value was NULL -- empty slot has been found,
	 * otherwise same state was found in hash.
	 */
	if (st == NULL) {
		hash_dprintf(" - ADDED");
		found = 1;
		state_hashtable[hash] = state;
		++used_hash_entries;
	} else
		hash_dprintf(" - OLD");

	dprintf("\n");

	return found;
}

/** 
 * @brief Prints hash statistics: used entries, collisions, etc.
 */
void state_hash_stats(void)
{
	iprintf("\tState hash:\n");
	iprintf("\t\tEntries:       %d\n", HASHTABLE_SIZE);
	iprintf("\t\tUsed:          %d (%.1f%%)\n", 
			used_hash_entries, used_hash_entries*100.f/HASHTABLE_SIZE);
	iprintf("\t\tCollisions:    %d (%.1f%%)\n", 
			hash_collisions, hash_collisions*100.f/used_hash_entries);
	iprintf("\t\tAvg col. len.: %.1f\n", 
			hash_collision_shifts*1.f/hash_collisions);
}

#else

#endif
