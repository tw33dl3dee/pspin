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

/*
 * Hash usage statistics
 */
/**
 * Total hash entries used
 */
static uint64_t used_hash_entries;
/**
 * Number of hash collisions (on first store attempt)
 */
static uint64_t hash_collisions;
/**
 * Average number of subsequent collisions
 */
static uint64_t hash_collision_shifts;
/**
 * Minimal state size stored
 */
static size_t min_state_size = UINT_MAX;
/**
 * Maximal state size stored
 */
static size_t max_state_size;
/**
 * Average state size
 */
static uint64_t total_state_size;
#ifndef FULLSTATE
/**
 * Maximum size occupied by states on BFS queue
 */
static size_t max_bfs_state_size;
#endif

/** 
 * @brief Prints hash statistics: used entries, collisions, etc.
 */
void state_hash_stats(void)
{
	iprintf("\tState hash:\n");
	iprintf("\t\tEntries:       " HASH_FMT "\n", HASHTABLE_LENGTH);
	iprintf("\t\tUsed:          %.0f (%.1f%%)\n", 
			(double)used_hash_entries, used_hash_entries*100./HASHTABLE_LENGTH);
	iprintf("\t\tCollisions:    %.0f (%.1f%%)\n", 
			(double)hash_collisions, hash_collisions*100./used_hash_entries);
	iprintf("\t\tAvg col. len.: %.1f\n", 
			hash_collision_shifts*1./hash_collisions);

	iprintf("\tState size:\n");
	iprintf("\t\tMin:           %zd\n", min_state_size);
	iprintf("\t\tMax:           %zd\n", max_state_size);
	iprintf("\t\tAvg:           %.1f\n", total_state_size*1./used_hash_entries);

	iprintf("\tMemory usage:\n");
	iprintf("\t\tHashtable:     %.1f MiB\n", HASHTABLE_SIZE*1./MiB);
#ifdef FULLSTATE
	iprintf("\t\tVisited:       %.1f MiB\n", total_state_size*1./MiB);
#else
	iprintf("\t\tBFS queue:     %.1f MiB\n", max_bfs_state_size*1./MiB);
#endif
}

/** 
 * @brief Prints intermediate hash statistics
 */
void state_hash_inter_stats(void)
{
	iprintf(" (hash use %.1f%%, collisions %.1f%%, "
#ifdef FULLSTATE
	        "visited: %.1f MiB"
#else
	        "BFS: %.1f MiB"
#endif
	        ")",
	        used_hash_entries*100./HASHTABLE_LENGTH,
	        hash_collisions*100./used_hash_entries,
#ifdef FULLSTATE
	        total_state_size*1./MiB
#else
	        max_bfs_state_size*1./MiB
#endif
			);
}

#if defined(FULLSTATE)

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


/** 
 * @brief Initializes hash table, allocating memory for it.
 * 
 * @return 0 on success, -1 if allocation failed.
 */
int state_hash_init()
{
	state_hashtable = calloc(sizeof(struct State *), HASHTABLE_LENGTH);
	if (state_hashtable == NULL) {
		printf("FAILED TO ALLOC %ld BYTES HASHTABLE\n", HASHTABLE_SIZE);
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
 * @param add_action Action to perform when adding state to hash
 * 
 * @return 1 if new state was added, 0 if it was present.
 */
int state_hash_add(struct State *state, enum HashAddAction add_action)
{
	state_hash_t hash = STATE_TABLE_HASH(state, 0);
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
		 * Open addressing with quadratic probes: slot, slot+1, slot+3, slot+6,..
		 */
		hash += ++offset;
		hash %= HASHTABLE_LENGTH;
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
		switch (add_action) {
		case BfsAddCopy:
			state = copy_state(state);
		case BfsAdd:
			BFS_ADD(state);
		case BfsNoAdd:
			state_hashtable[hash] = state;
		}

		total_state_size += STATESIZE(state);
		min_state_size = (min_state_size < STATESIZE(state)) ? min_state_size : STATESIZE(state);
		max_state_size = (max_state_size > STATESIZE(state)) ? max_state_size : STATESIZE(state);

		hash_dprintf(" - ADDED");
		++used_hash_entries;
	} else {
		found = 1;
		hash_dprintf(" - OLD");
	}

	dprintf("\n");

	return !found;
}

#elif defined(BITSTATE)

/* 
 * Bitstate hashing: each state is stored as BITSTATE_HASH_COUNT bits in hashtable.
 * When all bits are set, state is present in hash (may be a false positive).
 * When some bits are set, and other aren't, it's counted as
 * hash collision (for statistics and to estimate state dispersion quality).
 */

/**
 * Bitstate hash table
 */
static unsigned char *state_hashtable;

/** 
 * @brief Initializes hash table, allocating memory for it.
 * 
 * @return 0 on success, -1 if allocation failed.
 */
int state_hash_init()
{
	state_hashtable = calloc(1, HASHTABLE_SIZE);
	if (state_hashtable == NULL) {
		printf("FAILED TO ALLOC %ld BYTES HASHTABLE\n", HASHTABLE_SIZE);
		return -1;
	}
	return 0;
}

/** 
 * @brief Lookups state and hash table, adding new if none was found.
 *
 * New state is immediately pushed to BFS.
 * 
 * @param state state structure
 * @param add_action Action to perform when adding state to hash
 * 
 * @return 1 if new state was added, 0 if it was present.
 */
int state_hash_add(struct State *state, enum HashAddAction add_action)
{
	state_hash_t hash0 = STATE_TABLE_HASH(state, 0);
	state_hash_t hash = hash0;
	int found = 0;

	hash_dprintf("State hash (" HASH_FMT ")", hash0);
	dump_dprintf(" ");
	hexdump_state(state);

	/*
	 * Check each bit, setting it to 1.
	 */
	for (int i = 0; i < BITSTATE_HASH_COUNT; 
		 ++i, hash = STATE_TABLE_HASH(state, i)) {
		hash_dprintf(" (" HASH_FMT ")", hash);
		if (BIT_TEST(state_hashtable, hash))
			++found;
		else
			BIT_SET(state_hashtable, hash);
	}

	if (found < BITSTATE_HASH_COUNT) {
		/*
		 * Not all bits set -- new state 
		 */
		if (found > 0) {
			/*
			 * ... but some bits set -- possible collision 
			 */
			hash_dprintf(" {COLLISION: %d/%d bits set}", found, BITSTATE_HASH_COUNT);
			hash_collisions++;
			hash_collision_shifts += found;
		}

		switch (add_action) {
		case BfsAddCopy:
			state = copy_state(state);
		case BfsAdd:
			BFS_ADD(state);
			if (max_bfs_state_size < BFS_CUR_SIZE())
				max_bfs_state_size = BFS_CUR_SIZE();
		case BfsNoAdd:
			break;
		}

		total_state_size += BITSTATE_HASH_COUNT*STATESIZE(state);
		min_state_size = (min_state_size < STATESIZE(state)) ? min_state_size : STATESIZE(state);
		max_state_size = (max_state_size > STATESIZE(state)) ? max_state_size : STATESIZE(state);

		hash_dprintf(" - ADDED");
		used_hash_entries += BITSTATE_HASH_COUNT;
	}
	else 
		/*
		 * All bits set -- old state 
		 */
		hash_dprintf(" - OLD");

	dprintf("\n");

	return (found < BITSTATE_HASH_COUNT);
}

#endif
