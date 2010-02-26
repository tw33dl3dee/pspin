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

#include "state.h"
#include "state_hash.h"

void trace_state_begin(struct State *state)
{
	dprintf(" === We are on node %d ===\n", STATE_NODE_IDX(state, NODECOUNT));
}

void trace_state_new(struct State *state)
{
	dprintf(" --> To node %d <--\n", STATE_NODE_IDX(state, NODECOUNT));
}
