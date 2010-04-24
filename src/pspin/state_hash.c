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
 * Bytes used for storing hashtable
 */
static size_t hashtable_size;
/**
 * Total hash entries used
 */
static int used_hash_entries;
/**
 * Number of hash collisions (on first store attempt)
 */
static int hash_collisions;
/**
 * Average number of subsequent collisions
 */
static int hash_collision_shifts;
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
static size_t total_state_size;

/** 
 * @brief Prints hash statistics: used entries, collisions, etc.
 */
void state_hash_stats(void)
{
	iprintf("\tState hash:\n");
	iprintf("\t\tEntries:       %d\n", HASHTABLE_LENGTH);
	iprintf("\t\tUsed:          %d (%.1f%%)\n", 
			used_hash_entries, used_hash_entries*100.f/HASHTABLE_LENGTH);
	iprintf("\t\tCollisions:    %d (%.1f%%)\n", 
			hash_collisions, hash_collisions*100.f/used_hash_entries);
	iprintf("\t\tAvg col. len.: %.1f\n", 
			hash_collision_shifts*1.f/hash_collisions);

	iprintf("\tState size:\n");
	iprintf("\t\tMin:           %zd\n", min_state_size);
	iprintf("\t\tMax:           %zd\n", max_state_size);
	iprintf("\t\tAvg:           %.1f\n", total_state_size*1.0f/used_hash_entries);
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
	hashtable_size = sizeof(struct State *)*HASHTABLE_LENGTH;
	state_hashtable = calloc(sizeof(struct State *), HASHTABLE_LENGTH);
	if (state_hashtable == NULL) {
		printf("FAILED TO ALLOC %d BYTES HASHTABLE\n", hashtable_size);
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
	state_hash_t hash = STATE_HASH(state, 0) % HASHTABLE_LENGTH;
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
	hashtable_size = CHAR_BIT*HASHTABLE_LENGTH;
	state_hashtable = calloc(1, hashtable_size);
	if (state_hashtable == NULL) {
		printf("FAILED TO ALLOC %d BYTES HASHTABLE\n", hashtable_size);
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
	state_hash_t hash0 = STATE_HASH(state, 0) % HASHTABLE_LENGTH;
	state_hash_t hash = hash0;
	int found = 0;

	hash_dprintf("State hash (" HASH_FMT ")", hash0);
	dump_dprintf(" ");
	hexdump_state(state);

	/*
	 * Check each bit, setting it to 1.
	 */
	for (int i = 0; i < BITSTATE_HASH_COUNT; 
		 hash = STATE_HASH(state, ++i) % HASHTABLE_LENGTH) {
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
		case BfsNoAdd:
			break;
		}

		total_state_size += STATESIZE(state);
		min_state_size = (min_state_size < STATESIZE(state)) ? min_state_size : STATESIZE(state);
		max_state_size = (max_state_size > STATESIZE(state)) ? max_state_size : STATESIZE(state);

		hash_dprintf(" - ADDED");
		++used_hash_entries;
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
