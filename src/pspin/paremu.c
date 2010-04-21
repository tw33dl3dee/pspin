/**
 * @file   paremu.c
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Thu Feb 25 13:18:12 2010
 * 
 * @brief  Sequential statespace driver with parallel execution emulation.
 * 
 * 
 */

#ifdef MPI
#	error "MPI macro must not be defined in emulation version"
#endif

#include <assert.h>
#include <string.h>
#include <time.h>

#include "config.h"
#include "state.h"
#include "state_hash.h"
#include "bfs.h"
#include "debug.h"

static int cur_node_idx;
static int states_per_node[NODECOUNT];
static int state_count;
static int trans_count;
static int xnode_count;
static int max_bfs_size;

static void trace_state_begin(struct State *state)
{
	cur_node_idx = STATE_NODE_IDX(state, NODECOUNT);
	states_per_node[cur_node_idx]++;
	state_count++;
}

static void trace_state_new(struct State *state)
{
	int node_idx = STATE_NODE_IDX(state, NODECOUNT);
	if (node_idx != cur_node_idx) {
		state_dprintf("Message: node %d --> node %d \n", cur_node_idx, node_idx);
		xnode_count++;
	}
	if (BFS_CUR_LEN() > max_bfs_size)
		max_bfs_size = BFS_CUR_LEN();
	trans_count++;
}

static void trace_summary()
{
	float run_time = clock()*1.f/CLOCKS_PER_SEC;

	iprintf("Emulation summary:\n");

	iprintf("\tTransitions taken: %d (%.1f/sec)\n"
			"\tMessages passed:   %d (%.2f%%)\n",
			trans_count, trans_count/run_time,
			xnode_count, xnode_count*100.f/trans_count);

	iprintf("\tStates:\n"
			"\t\tTotal:   %d (%.1f/sec)\n",
			state_count, state_count/run_time);
	
	int states_max = 0, states_min = states_per_node[0];
	for (int i = 0; i < NODECOUNT; ++i) {
		if (states_min > states_per_node[i])
			states_min = states_per_node[i];
		if (states_max < states_per_node[i])
			states_max = states_per_node[i];
		iprintf("\t\tNode %2d: %d (%.1f%%)\n",
				i, states_per_node[i], states_per_node[i]*100.f/state_count);
	}
	iprintf("\t\tMin/max: %.2f\n", 
			states_min*1.f/states_max);

	iprintf("\tBFS max size:      %d (%.2f%% st, %.2f%% tr)\n",
			max_bfs_size, 
			max_bfs_size*100.f/state_count, max_bfs_size*100.f/trans_count);

	state_hash_stats();
}

/** 
 * @brief Checks if state is already in hash table, adds it otherwise
 * 
 * @param state State structure
 */
static void queue_new_state(struct State *state)
{
	/*
	 * This will already push new state to BFS.
	 */
	state_hash_add(state, /* don't copy */ 0);
}

/** 
 * @brief Perform BFS search and build hash-table of all states
 * 
 */
static void bfs(void)
{
	struct State *init_state;
	struct State *cur_state, *next_state;
	transitions_t transitions;

	BFS_INIT();

	state_dprintf("Initial state:");
	init_state = create_init_state();
	queue_new_state(init_state);
	transitions = init_transitions();

	while ((cur_state = BFS_TAKE()) != NULL) {
		int pid = 0;
#ifdef ENDSTATE
		int transitions_possible = 0;
#endif

		state_dprintf("---------------------------------\n");
		trace_state_begin(cur_state);

		state_dprintf("Transitions from state:\n");
#ifdef STATE_DEBUG
		dump_state(cur_state);
#endif

		FOREACH_PROCESS(cur_state, ++pid) {
			state_dprintf("Transitions for process %d", pid);
			if (STATEATOMIC(cur_state) >= 0 && 
				STATEATOMIC(cur_state) != pid) {
				state_dprintf(" SKIPPED, in ATOMIC context\n");
				continue;
			} else
				state_dprintf(":\n");

			FOREACH_TRANSITION(transitions, src_ip, dest_ip) {
				state_dprintf("\t%d -> %d ", src_ip, dest_ip);

				switch (do_transition(pid, dest_ip, cur_state, current, &next_state)) {
				case TransitionCausedAbort:
					goto aborted;

				case TransitionPassed:
#ifdef ENDSTATE
					++transitions_possible;
#endif

					state_dprintf("New state:\n");
#ifdef STATE_DEBUG
					dump_state(next_state);
#endif

					assert(next_state != NULL);
					queue_new_state(next_state);
					
					trace_state_new(next_state);
					break;

				case TransitionBlocked:
					break;
				}
			}
		}

#ifdef ENDSTATE
		if (!transitions_possible) {
			state_dprintf("End-state, performing validity check...\n");
			if (check_endstate(cur_state) < 0)
				goto aborted;
		}
#endif
	}

 aborted:
	state_dprintf("---------------------------------\n");

	trace_summary();
}

int main()
{
	bfs();
	return 0;
}
