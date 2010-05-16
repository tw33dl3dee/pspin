/**
 * @file   state.h
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Mon Dec 28 19:52:41 2009
 * 
 * @brief  
 * 
 * 
 */

#ifndef _STATE_H_
#define _STATE_H_

#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "channel.h"

/**
 * General process structure
 */
struct Process {
	/**
	 * IP (0-based)
	 */
    unsigned char _ip ;
	/**
	 * Proctype (0-based)
	 */
    unsigned char _proctype ;
	/**
	 * Other data (process-specific)
	 */
	char data[1];
};

#define STATE_DECL
#include STATEGEN_FILE
#undef  STATE_DECL

#define PROC_DECL
#include STATEGEN_FILE
#undef  PROC_DECL

/**
 * Size required to hold state's size
 */
#define STATESIZE_SIZE (sizeof(STATESIZE(NULL)))

/**
 * Typename that stores state's size
 */
#define STATESIZE_TYPE __typeof__(STATESIZE(NULL))

/**
 * Copies state structure as byte array
 */
#define COPY_STATE(dst, src)					\
	memcpy(dst, src, STATESIZE(src));

/**
 * Retrieves process substate at specific offset
 */
#define PROC_BY_OFFSET(state, offset)				\
	(struct Process *)((char *)(state) + (offset))

/**
 * Returns offset of process substate inside whole state
 */
#define PROC_OFFSET(proc, state)				\
	((char *)(proc) - (char *)(state))

/**
 * Retrieves state of the first active process
 */
#define FIRST_PROC(state) (struct Process *)(state)->_procs

/**
 * Enumerates processes (referred to as `current') inside `state' executing
 * `increment_expr' on each new process before changing `current'.
 */
#define FOREACH_PROCESS(state, increment_expr)							\
	for (struct Process													\
			 *base = FIRST_PROC(state),									\
			 *current = base;											\
		 (char *)current - (char *)state < STATESIZE(state);			\
		 (increment_expr),												\
			 current = PROC_BY_OFFSET(current, PROCSIZE(current)))

/**
 * Enumerates all transitions (by `src_ip' and `dest_ip') for process
 * specified by `current'.
 */
#define FOREACH_TRANSITION(transitions, src_ip, dest_ip)				\
	for (int i = 0, src_ip = PROCIP(current), dest_ip = 0;				\
		 /* PROCIP(current) *may* change during loop */					\
		 (dest_ip = transitions[PROCTYPE(current)][src_ip][i]) != 0;	\
		 ++i)

/**
 * Transitions array: proctype -> oldip -> [newips, zero-terminated]
 */
typedef int ***transitions_t;

/**
 * Result of transition attempt
 *
 * @sa do_transition
 */
enum TransitionResult {
	TransitionBlocked = -1,		///< Transition impossible
	TransitionPassed,			///< Transition possible and was performed
	TransitionCausedAbort,		///< Transition was performed and resulted in abortion
};

/*
 * Exported to statespace drivers (sequential/parallel MPI/etc).
 */

transitions_t init_transitions(void);
struct State *create_init_state(void);
struct State *copy_state(const struct State *state);
void dump_state(struct State *state);
void hexdump_state(struct State *state);

enum TransitionResult 
do_transition(int pid, int dest_ip,
			  struct State *state, struct Process *current, 
			  struct State **next_state);

int
check_endstate(struct State *state);
		
#endif /* _STATE_H_ */
