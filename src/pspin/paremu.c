/**
 * @file   paremu.c
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Thu Feb 25 13:18:12 2010
 * 
 * @brief  Parallel exection emulation and statistics gathering.
 * 
 * 
 */

#include <stdlib.h>
#include <stdio.h>
#include <time.h>

#include "state.h"
#include "state_hash.h"
#include "bfs.h"

static int cur_node_idx;
static int states_per_node[NODECOUNT];
static int state_count;
static int trans_count;
static int xnode_count;
static int max_bfs_size;

void trace_state_begin(struct State *state)
{
	cur_node_idx = STATE_NODE_IDX(state, NODECOUNT);
	states_per_node[cur_node_idx]++;
	state_count++;
}

void trace_state_new(struct State *state)
{
	int node_idx = STATE_NODE_IDX(state, NODECOUNT);
	if (node_idx != cur_node_idx) {
		dprintf("Message: node %d --> node %d \n", cur_node_idx, node_idx);
		xnode_count++;
	}
	if (BFS_LEN() > max_bfs_size)
		max_bfs_size = BFS_LEN();
	trans_count++;
}

void trace_summary()
{
	float run_time = clock()*1.f/CLOCKS_PER_SEC;

	dprintf("Emulation summary:\n");

	dprintf("\tTransitions taken: %d (%.1f/sec)\n"
			"\tMessages passed:   %d (%.2f%%)\n",
			trans_count, trans_count/run_time,
			xnode_count, xnode_count*100.f/trans_count);

	dprintf("\tStates:\n"
			"\t\tTotal:   %d (%.1f/sec)\n",
			state_count, state_count/run_time);
	
	int states_max = 0, states_min = states_per_node[0];
	for (int i = 0; i < NODECOUNT; ++i) {
		if (states_min > states_per_node[i])
			states_min = states_per_node[i];
		if (states_max < states_per_node[i])
			states_max = states_per_node[i];
		dprintf("\t\tNode %2d: %d (%.1f%%)\n",
				i, states_per_node[i], states_per_node[i]*100.f/state_count);
	}
	dprintf("\t\tMin/max: %.2f\n", 
			states_min*1.f/states_max);

	dprintf("\tBFS max size:      %d (%.2f%% st, %.2f%% tr)\n",
			max_bfs_size, 
			max_bfs_size*100.f/state_count, max_bfs_size*100.f/trans_count);
}
