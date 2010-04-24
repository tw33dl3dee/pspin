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
#include "bfs.h"

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
static size_t min_state_size = UINT_MAX;
static size_t max_state_size;
static size_t total_state_size;

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
 * New state is immediately pushed to BFS.
 * 
 * @param state state structure
 * @param do_copy If non-zero, new state is copied before adding it to hash
 * 
 * @return 1 if new state was added, 0 if it was present.
 */
int state_hash_add(struct State *state, int do_copy)
{
	state_hash_t hash = STATE_HASH(state, 0) % HASHTABLE_SIZE;
	state_hash_t offset = 0;
	struct State *st;
	int found = 0;
	int had_collisions = 0;

	hash_dprintf("State hash (" HASH_FMT ")", hash);

	dump_dprintf(" ");
	hexdump_state(state);

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

		dump_dprintf(" := ");
		hexdump_state(st);
	}

	if (had_collisions)
		hash_collisions++;

	/*
	 * If last slot value was NULL -- empty slot has been found,
	 * otherwise same state was found in hash.
	 */
	if (st == NULL) {
		found = 1;
		state_hashtable[hash] = do_copy ? copy_state(state) : state;
		BFS_ADD(state_hashtable[hash]);

		total_state_size += STATESIZE(state);
		min_state_size = (min_state_size < STATESIZE(state)) ? min_state_size : STATESIZE(state);
		max_state_size = (max_state_size > STATESIZE(state)) ? max_state_size : STATESIZE(state);

		hash_dprintf(" - ADDED");
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

	iprintf("\tState size:\n");
	iprintf("\t\tMin:           %zd\n", min_state_size);
	iprintf("\t\tMax:           %zd\n", max_state_size);
	iprintf("\t\tAvg:           %.1f\n", total_state_size*1.0f/used_hash_entries);
}

#else

#endif
