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
 * @brief N-th hash function
 * 
 * Macro invokes N-th hash functions (for multihash purposes)
 * 
 * @param key Data to hash
 * @param len Data size
 * @param num Hash function number (0..)
 * 
 * @return Hash value
 */
#define HASH(data, len, num)											\
	murmur_hash(data, len, ((state_hash_t)1<<(num+1))+((state_hash_t)(-1)>>(num+1)))

/** 
 * @brief N-th hash value of state
 * 
 * @param state State to hash
 * @param num Hash function number (0..)
 * 
 * @return State hash value
 */
#define STATE_HASH(state, num) HASH(state, STATESIZE(state), num)

/*
 * Bit functions 
 */
#define BIT_TEST(bits, number)  ((bits)[(number)/CHAR_BIT] &   (1 << (number)%CHAR_BIT))
#define BIT_SET(bits, number)   ((bits)[(number)/CHAR_BIT] |=  (1 << (number)%CHAR_BIT))
#define BIT_RESET(bits, number) ((bits)[(number)/CHAR_BIT] &= ~(1 << (number)%CHAR_BIT))

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

/*
 * Node partitioning function selection.
 * Function that evaluates to node number which given state is stored on
 */
#if defined(STATE_PARTITION_HASH)
/*
 * Use full state hash as partitioning function
 */
#	define STATE_NODE_IDX(state, node_count) (STATE_HASH(state, 1)%(node_count))
#elif defined(STATE_PARTITION_FIRST_PROC)
/*
 * Use partial state hash (first process data hash) as partitioning function
 */
#	define STATE_NODE_IDX(state, node_count)		\
	({												\
		struct Process *proc = FIRST_PROC(state);	\
		HASH(proc, PROCSIZE(proc), 1)%(node_count);	\
	})
#endif

#endif /* _HASH_H_ */
