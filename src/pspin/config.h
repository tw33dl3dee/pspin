/**
 * @file   config.h
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Mon Apr 19 20:12:43 2010
 * 
 * @brief  Compile-time configuration options.
 * 
 */

#ifndef _PSPIN_CONFIG_H
#define _PSPIN_CONFIG_H

/*
 * Size constants
 */
#define kiB 1024
#define MiB (kiB*kiB)
#define GiB (MiB*kiB)

/*
 * Emulation-specific options 
 */
#ifdef EMULATION
/**
 * Number of nodes that are emulated by statistic gatherer
 */
#	define NODECOUNT 4
#endif

/*
 * MPI-specific options 
 */
#ifdef MPI
#endif

/**
 * If defined, endstate validness is checked
 */
#undef ENDSTATE

/*
 * Node partitioning function selection
 */

/**
 * Use whole state hash as partitioning function
 */
#define STATE_PARTITION_HASH
/**
 * Use first process hash as partitioning function
 */
#undef  STATE_PARTITION_FIRST_PROC

/* 
 * Hashing scheme selection
 */
/**
 * Use bitstate hashing
 */
#undef BITSTATE
/**
 * Use hashcompact hashing
 */
#undef HASHCOMPACT
/**
 * Use full state hashing
 */
#define FULLSTATE

/*
 * Hashtable and hashing function options 
 */

/**
 * Size of hashtable (entries)
 */
#define HASHTABLE_SIZE (1*MiB + 1)

#ifdef FULLSTATE
/**
 * With fullstate hashing, states from network queue are pushed immediately to local queue.
 *
 * This is not the case with bitstate and hashcompact hashing, where it would be waste of
 * statespace (because storing full states is avoided where possible).
 */
#	define NETWORK_TO_LOCAL_QUEUE
/**
 * Size of memory which is allocated to store states, both visited and in-queue (in bytes).
 */
#	define STATESPACE_SIZE (128*MiB)
#else
/**
 * Size of BFS queue (bytes)
 *
 * When bitstate or hashcompact hashing is used, BFS is a separate state queue.
 * With fullstate hashing, visited states and BFS are stored continously, so this is unused.
 */
#	define BFS_QUEUE_SIZE  1*MiB
#endif

#ifdef BITSTATE 
/**
 * Number of hash functions to use for bit-hashing
 */
#	define BITSTATE_HASH_COUNT 2
#endif

#ifdef HASHCOMPACT
/**
 * Size of stored hashes for hashcompact method (bits)
 */
#	define HASHCOMPACT_BITS 64
#endif

#endif /* _PSPIN_CONFIG_H */
