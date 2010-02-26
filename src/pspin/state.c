/**
 * @file   state.c
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Mon Dec 28 19:37:08 2009
 * 
 * @brief  
 * 
 * 
 */

#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>

#include "state.h"
#include "bfs.h"
#include "state_hash.h"

/** 
 * @brief Initialize transition tables
 * @return Head of transition table
 */
transitions_t init_transitions(void)
{
	transitions_t transitions;

#define TRANSITIONS_INIT
#include CODEGEN_FILE
#undef  TRANSITIONS_INIT

	return transitions;
}

/** 
 * @brief Allocates new state structure
 * 
 * @param svsize State size (in bytes)
 * @param zero If nonzero, zeroes all state bits (except size field)
 * 
 * @return State structure (or NULL if no memory available)
 */
struct State *alloc_state(size_t svsize, int zero)
{
	struct State *state; 
	//dprintf(" (alloc new state of size %d) ", svsize);
	state = malloc(svsize); 
	if (state)
		STATESIZE(state) = svsize;
	return state;
}

/** 
 * @brief Initializes process state substructure
 * 
 * @param current Newly allocated process structure
 * @param proctype Proctype (is saved to `current')
 */
void init_process(struct Process *current, int proctype)
{
	PROCTYPE(current) = proctype;
	PROCIP(current) = 0;
	
#define PROCSTATE_INIT
#include CODEGEN_FILE
#undef  PROCSTATE_INIT
}

/** 
 * @brief Creates initial state structure, initializing globals and active proctypes.
 */
struct State *create_init_state(void)
{
	struct State *state;
	struct Process *proc;

	int svsize = (char *)(&state->_procs) - (char *)state;
	for (int ptype = 0; ptype < NPROCTYPE; ++ptype) 
		svsize += procsizes[ptype]*procactive[ptype];

	state = alloc_state(svsize, 1);

#define STATE_INIT
#include CODEGEN_FILE
#undef  STATE_INIT

	proc = FIRST_PROC(state);
	for (int ptype = 0; ptype < NPROCTYPE; ++ptype)
		for (int i = 0; i < procactive[ptype]; ++i) {
			init_process(proc, ptype);
			proc = PROC_BY_OFFSET(proc, procsizes[ptype]);
		}

	return state;
}

/** 
 * @brief Copies state structure
 */
struct State *copy_state(const struct State *state)
{
	struct State *new_state = alloc_state(STATESIZE(state), 0);
	if (new_state != NULL)
		memcpy(new_state, state, STATESIZE(state));
	return new_state;
}

/** 
 * @brief Copies state structure, adding new proctype to it
 * 
 * @param state Original state
 * @param proctype Proctype to add
 *
 * New proctype is added at the end
 * 
 * @return New state structure
 */
struct State *copy_state_add_process(const struct State *state, int proctype)
{
	assert(proctype < NPROCTYPE);
	struct State *new_state = alloc_state(STATESIZE(state) + procsizes[proctype], 0);
	if (new_state != NULL) {
		memcpy(new_state, state, STATESIZE(state));
		init_process(PROC_BY_OFFSET(new_state, STATESIZE(state)), proctype);
	}
	return new_state;
}

/** 
 * @brief Perform transition, if possible.
 * 
 * @param pid Pid of current process
 * @param dest_ip IP to transition process to
 * @param state Current state
 * @param current Current process state
 * @param next_state Next state is stored here if transition passes
 * 
 * @return 0 if transition performed, -1 if it was blocked
 */
int do_transition(int pid, int dest_ip,
				  struct State *state, struct Process *current, 
				  struct State **next_state)
{
	int current_offset;

#define RECORD_STEP(msg) dprintf(" PASSED\nPerforming step: *** %s ***\n", msg);
#define COPY_STATE()										\
	*next_state = copy_state(state);						\
	current_offset = PROC_OFFSET(current, state);			\
	state = *next_state;									\
	current = PROC_BY_OFFSET(state, current_offset);
#define COPY_STATE_NEW_PROC(proctype)						\
	*next_state = copy_state_add_process(state, proctype);	\
	current_offset = PROC_OFFSET(current, state);			\
	state = *next_state;									\
	current = PROC_BY_OFFSET(state, current_offset);	
#define ASSERT(expr, repr)									\
	if (!(expr)) {											\
		fprintf(stderr, "ASSERTION `%s' FAILED\n", repr);	\
		abort();											\
	}														\


#define TRANSITIONS
#include CODEGEN_FILE
#undef  TRANSITIONS

 passed:
	PROCIP(current) = dest_ip;
	return 0;
 blocked:
	dprintf(" BLOCKED\n");
	return -1;
}

/** 
 * @brief Dumps global and per-process state variables
 * 
 * @param state State to dump
 */
void dump_state(struct State *state) 
{
#define STATE_DUMP
#include CODEGEN_FILE
#undef  STATE_DUMP

	int pid = 0;
	FOREACH_PROCESS(state, ++pid) {
		dprintf("\t-Process %d:\n", pid);
#define PROCSTATE_DUMP
#include CODEGEN_FILE
#undef  PROCSTATE_DUMP
	}
}

/** 
 * @brief Checks if state is already in hash table, adds it otherwise
 * 
 * @param state State structure
 */
void queue_new_state(struct State *state)
{
	int is_new = state_hash_add(state);
	if (is_new) {
		dprintf(" - ADDED");
		BFS_ADD(state);
	}
	dprintf("\n");
}

/** 
 * @brief Perform BFS search and build hash-table of all states
 * 
 */
void bfs(void)
{
	struct State *init_state;
	struct State *cur_state, *next_state;
	transitions_t transitions;

	BFS_INIT();

	dprintf("Initial state:");
	init_state = create_init_state();
	queue_new_state(init_state);
	transitions = init_transitions();

	while ((cur_state = BFS_TAKE()) != NULL) {
		int pid = 0;

		trace_state_begin(cur_state);

		dprintf("Transitions from state:\n");
		dump_state(cur_state);

		FOREACH_PROCESS(cur_state, ++pid) {
			dprintf("Transitions for process %d\n", pid);

			FOREACH_TRANSITION(transitions, src_ip, dest_ip) {
				dprintf("\t%d -> %d ", src_ip, dest_ip);

				if (do_transition(pid, dest_ip, cur_state, current, &next_state) < 0)
					continue;

				dprintf("New state:\n");
				dump_state(next_state);

				assert(next_state != NULL);
				queue_new_state(next_state);

				trace_state_new(next_state);
			}
		}

		dprintf("---------------------------------\n");
	}
}

int main()
{
	bfs();
	return 0;
}
