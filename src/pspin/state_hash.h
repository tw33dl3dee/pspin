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

typedef unsigned long long state_hash_t;

#define HASH_FMT "%llu"

/**
 * Bernstein hash
 */
#define HASH(data, len)												\
	({																\
		state_hash_t hash = 5381;									\
		for (int i = 0; i < (len); ++i)								\
			hash = (hash << 5) + hash  + ((char *)data)[i];			\
		(state_hash_t)hash;											\
	})

#define STATE_HASH(state) HASH(state, STATESIZE(state))

#define BIT_TEST(bits, number)  ((bits)[(number)/8] &   (1 << (number)%8))
#define BIT_SET(bits, number)   ((bits)[(number)/8] |=  (1 << (number)%8))
#define BIT_RESET(bits, number) ((bits)[(number)/8] &= ~(1 << (number)%8))

extern int state_hash_add(struct State *state, int do_copy);
extern int state_hash_init();
extern void state_hash_stats(void);

#if defined(STATE_PARTITION_HASH)
#	define STATE_NODE_IDX(state, node_count) (STATE_HASH(state)%(node_count))
#elif defined(STATE_PARTITION_FIRST_PROC)
#	define STATE_NODE_IDX(state, node_count)		\
	({												\
		struct Process *proc = FIRST_PROC(state);	\
		HASH(proc, PROCSIZE(proc))%(node_count);	\
	})
#endif

#endif /* _HASH_H_ */
