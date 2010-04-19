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

#endif /* _PSPIN_CONFIG_H */
