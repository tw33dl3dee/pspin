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

#define UTYPE_DECL
#include STATEGEN_FILE
#undef  UTYPE_DECL

#define STATE_DECL
#include STATEGEN_FILE
#undef  STATE_DECL

#define PROC_DECL
#include STATEGEN_FILE
#undef  PROC_DECL

/**
 * General process structure
 */
struct Process {
	/**
	 * IP (0-based)
	 */
#if PROC_IP_BYTES == 2
    short _ip;
#elif PROC_IP_BYTES == 1
    unsigned char _ip;
#else
#	error Unsupported IP size
#endif
	/**
	 * Proctype (0-based)
	 */
    unsigned char _proctype;
	/**
	 * Other data (process-specific)
	 */
	char data[0];
};

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
 * `current' may be altered inside loop body.
 */
#define FOREACH_PROCESS(state, increment_expr)							\
	for (struct Process													\
	         *base = FIRST_PROC(state),									\
	         *current_save = base,										\
	         *current = base;											\
		 (char *)current - (char *)state < STATESIZE(state);			\
		 (increment_expr),												\
	         current_save = current =									\
	         PROC_BY_OFFSET(current_save, PROCSIZE(current)))

/**
 * Enumerates up to `process_count` processes (referred to as `current') inside `state'.
 * Requires `counter` variable to be predeclared as "int" and initialized with 0.
 */
#define FOREACH_N_PROCESSES(state, process_count, counter)				\
	for (struct Process *current = FIRST_PROC(state);					\
		 counter < process_count;										\
		 ++counter,														\
			 current = PROC_BY_OFFSET(current, PROCSIZE(current)))

/**
 * Enumerates all transitions (by `src_ip' and `dest_ip') for process
 * specified by `process'.
 */
#define FOREACH_TRANSITION(transitions, process, src_ip, dest_ip)		\
	for (int i = 0, src_ip = PROCIP(process), dest_ip = 0;				\
		 /* PROCIP(process) *may* change during loop */					\
		 (dest_ip = transitions[PROCTYPE(process)][src_ip][i]) != 0;	\
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
void edump_state(struct State *state);
void hexdump_state(struct State *state);

extern int use_pml_printf;

enum TransitionResult 
do_transition(transitions_t transitions,
              int pid, int dest_ip,
			  struct State *state, struct Process *current, 
			  struct State **next_state);

int
check_endstate(struct State *state);
		
#endif /* _STATE_H_ */
