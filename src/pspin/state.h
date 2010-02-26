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
	char data[0];
};

#define STATE_DECL
#include CODEGEN_FILE
#undef  STATE_DECL

#define PROC_DECL
#include CODEGEN_FILE
#undef  PROC_DECL

#define PROC_BY_OFFSET(state, offset)				\
	(struct Process *)((char *)(state) + (offset))

#define PROC_OFFSET(proc, state)				\
	((char *)(proc) - (char *)(state))

#define FIRST_PROC(state) (struct Process *)(state)->_procs

#define FOREACH_PROCESS(state, increment_expr)							\
	for (struct Process													\
			 *base = FIRST_PROC(state),									\
			 *current = base;											\
		 (char *)current - (char *)state < STATESIZE(state);			\
		 (increment_expr),												\
			 current = PROC_BY_OFFSET(current, PROCSIZE(current)))

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
 *  Tracing facilities
 */

#define dprintf printf

void trace_state_begin(struct State *state);
void trace_state_new(struct State *state);
		
#endif /* _STATE_H_ */
