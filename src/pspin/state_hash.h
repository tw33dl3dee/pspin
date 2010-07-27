/**
 * @file   hash.h
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Mon Feb 22 18:57:26 2010
 * 
 * @brief  Hashing functions and hashtable implementation.
 * 
 */

#ifndef _HASH_H_
#define _HASH_H_

#include "murmur_hash.h"

/** 
 * @brief Primary hash function
 * 
 * @param key Data to hash
 * @param len Data size
 * @param seed Hash seed
 * 
 * @return Hash value
 */
#define HASH(data, len, seed)					\
	murmur_hash(data, len, seed)

/** 
 * @brief Seed used for hash function number num
 */
#define SEED(num) ((hash_seed_t)1<<((num)+1))+((hash_seed_t)(-1)>>((num)+1))

/** 
 * @brief Hash value of state
 * 
 * @param state State to hash
 * @param seed Hash seed
 * 
 * @return State hash value
 */
#define STATE_HASH(state, seed) HASH(state, STATESIZE(state), seed)

/** 
 * @brief N-th hash value of state, mapped to 0..HASHTABLE_LENGTH-1
 * 
 * @param state State to hash
 * @param num Hash function number (0..)
 * 
 * @return State hash value in 0..HASHTABLE_LENGTH-1 range
 */
#define STATE_TABLE_HASH(state, num) (STATE_HASH(state, SEED(num)) % HASHTABLE_LENGTH)

/*
 * Bit functions 
 */
#define BIT_TEST(bits, number)  ((bits)[(number)/CHAR_BIT] &   (1 << (number)%CHAR_BIT))
#define BIT_SET(bits, number)   ((bits)[(number)/CHAR_BIT] |=  (1 << (number)%CHAR_BIT))
#define BIT_RESET(bits, number) ((bits)[(number)/CHAR_BIT] &= ~(1 << (number)%CHAR_BIT))

/*
 * Arithmetic 
 */
#define ROUNDUP(x, n) (x + ((x)%(n)?1:0))
#define ROUNDDOWN(x, n) ((x) - (x)%(n))

/*
 * Size of hashtable (entries) 
 */
#if defined(FULLSTATE)
#	define HASHTABLE_LENGTH ((state_hash_t)HASHTABLE_SIZE/sizeof(struct State *))
#elif defined(BITSTATE)
#	define HASHTABLE_LENGTH ((state_hash_t)HASHTABLE_SIZE*CHAR_BIT)
#endif

/**
 * Action to perform when adding new state to hash
 */
enum HashAddAction {
	BfsNoAdd = 0,			///< Do nothing
	BfsAdd,					///< Add to BFS queue
	BfsAddCopy,				///< Copy and add copy to BFS queue
};

extern int state_hash_add(struct State *state, enum HashAddAction add_action);
extern int state_hash_init();
extern void state_hash_stats(void);
extern void state_hash_inter_stats(void);

extern int dump_new_states;

/**
 * Initial hash seed used for hash-based partitioning
 */
#define PARTITION_HASH_SEED 0xA567B123

/*
 * Node partitioning function selection.
 * Function that evaluates to node number which given state is stored on
 */
#if defined(STATE_PARTITION_HASH)
/*
 * Use full state hash as partitioning function
 */
#	define STATE_NODE_IDX(state, node_count) (STATE_HASH(state, PARTITION_HASH_SEED)%(node_count))
#elif defined(STATE_PARTITION_PROC)
/*
 * Use partial state hash (first N processes data hash) as partitioning function
 */
#	define STATE_NODE_IDX(state, node_count)					\
	({															\
		state_hash_t seed = PARTITION_HASH_SEED;				\
		int pid = 0;											\
		FOREACH_N_PROCESSES(state, PARTITION_PROC_COUNT, pid)	\
		    seed = HASH(current, PROCSIZE(current), seed);		\
		seed%(node_count);										\
	})
#elif defined(STATE_PARTITION_PROC_NOIP)
/** 
 * Same without processes' IPs
 */
#	define STATE_NODE_IDX(state, node_count)							\
	({																	\
		state_hash_t seed = PARTITION_HASH_SEED;						\
		int pid = 0;													\
		FOREACH_N_PROCESSES(state, PARTITION_PROC_COUNT, pid)			\
		    seed = HASH(&current->data,									\
		                PROCSIZE(current) - sizeof(struct Process),		\
		                seed);                                          \
		seed%(node_count);												\
	})
#endif

#endif /* _HASH_H_ */
