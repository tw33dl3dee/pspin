/**
 * @file   state.c
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Mon Dec 28 19:37:08 2009
 * 
 * @brief  
 * 
 * 
 */

#define CODEGEN_FILE "../pmlparse/peterson3.c"

#include "state.h"

/** 
 * @brief Perform specified transition, if possible.
 * 
 * @param proctype Proctype index of current process
 * @param state Current state
 * @param current Current process state
 * @param next_state Next state (to be stored to)
 * @param next_current Current process state in `next_state` structure
 * 
 * @return 0 if transition performed, -1 if it was blocked
 */
int do_transition(int proctype, 
				  struct State *state, struct Process *current, 
				  struct State *next_state, struct Process *next_current)
{
#define RECORD_STEP(msg) printf("Performing step: %s\n", msg);
#define COPY_STATE								\
	*next_state = *state;						\
	state = next_state;							\
	current = next_current;

#define TRANSITIONS
#include CODEGEN_FILE
#undef  TRANSITIONS

 passed:
	return 0;
 blocked:
	return -1;
}
