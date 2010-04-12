/**
 * @file   parmpi.c
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Sun Mar 21 16:56:28 2010
 * 
 * @brief  Parallel statespace driver using MPI.
 * 
 */

#include <assert.h>
#include <mpi.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#include "state.h"
#include "state_hash.h"
#include "bfs.h"
#include "mpi_async.h"
#include "mpi_tags.h"
#include "debug.h"

int node_count;
int node_id;

/**
 * Used for nice debug log formatting.
 */
int output_flushed = 1;

#define MAX_STATESIZE 1024
#define MPI_QLEN      32

static int last_buf_no = -1;
static struct mpi_queue sendq, recvq;

static int state_count;
static int trans_count;
static int xnode_count;
static int max_bfs_size;
static double start_time;

static void trace_start()
{
	start_time = MPI_Wtime();
}

static void trace_state_begin(struct State *state)
{
	state_count++;
}

static void trace_state_new(struct State *state)
{
	if (BFS_LEN() > max_bfs_size)
		max_bfs_size = BFS_LEN();
	trans_count++;
}

static void trace_state_send(struct State *state, int node_idx)
{
	xnode_count++;
}

static void trace_summary()
{
	float run_time = MPI_Wtime() - start_time;

	state_dprintf("Parallel run summary:\n");

	state_dprintf("\tTransitions taken: %d (%.1f/sec)\n",
				  trans_count, trans_count/run_time);
	state_dprintf("\tMessages passed:   %d (%.2f%%)\n",
				  xnode_count, xnode_count*100.f/trans_count);
	state_dprintf("\tStates:            %d (%.1f/sec)\n",
			state_count, state_count/run_time);
	state_dprintf("\tBFS max size:      %d (%.2f%% st, %.2f%% tr)\n",
			max_bfs_size, 
			max_bfs_size*100.f/state_count, max_bfs_size*100.f/trans_count);
}

/** 
 * @brief Checks if state is already in hash table, adds it otherwise
 * 
 * @param state State structure
 */
static void queue_new_state(struct State *state)
{
	int state_node = STATE_NODE_IDX(state, node_count);

	mpi_dprintf("[Belongs to NODE %d] ", state_node);
	if (state_node != node_id) {
		int buf_no = mpi_async_get_buf(&sendq, 0);
		COPY_STATE(MPI_ASYNC_BUF(&sendq, buf_no, void), state);
		mpi_async_queue_buf(&sendq, buf_no, STATESIZE(state), MPI_CHAR, state_node, TagState);
		mpi_dprintf("[SENT]");
		trace_state_send(state, state_node);
	}
	else if (state_hash_add(state)) {
		state_dprintf(" - ADDED");
		BFS_ADD(state);
	}
	dprintf("\n");
}

static struct State *get_state(void)
{
	struct State *state;

	// @todo distributed termination

	/*
	 * First check if there are incoming messages 
	 * @todo Drain MPI queue into local queue instead of deque/put
	 */
	last_buf_no = mpi_async_deque_buf(&recvq, 1);
	if (last_buf_no != -1) {
		state = MPI_ASYNC_BUF(&recvq, last_buf_no, struct State);
		if (state_hash_add(state))
			return state;
	}
	/*
	 * Then check local queue 
	 */
	if ((state = BFS_TAKE()) != NULL)
		return state;
	/*
	 * Block and wait for new messages 
	 */
	for (;;) {
		last_buf_no = mpi_async_deque_buf(&recvq, 0);
		state = MPI_ASYNC_BUF(&recvq, last_buf_no, struct State);
		if (state_hash_add(state))
			return state;
	}
}

static void put_state(struct State *state)
{
	if (last_buf_no != -1) {
		mpi_dprintf("[RELEASE BUF %d]\n", last_buf_no);
		mpi_async_put_buf(&recvq, last_buf_no, MAX_STATESIZE, MPI_CHAR, MPI_ANY_SOURCE, MPI_ANY_TAG);
	}				  
}

/** 
 * @brief Perform DFS search and build hash-table of all states
 * 
 */
static void dfs(void)
{
	struct State *init_state;
	struct State *cur_state, *next_state;
	transitions_t transitions;

	BFS_INIT();

	mpi_async_send_start(&sendq, MPI_QLEN, MAX_STATESIZE);
	mpi_async_recv_start(&recvq, MPI_QLEN, MAX_STATESIZE);
	for (int i = 0; i < MPI_QLEN; ++i)
		mpi_async_put_buf(&recvq, i, MAX_STATESIZE, MPI_CHAR, MPI_ANY_SOURCE, MPI_ANY_TAG);

	trace_start();

	state_dprintf("Initial state: ");
	init_state = create_init_state();
	queue_new_state(init_state);
	transitions = init_transitions();

	while ((cur_state = get_state()) != NULL) {
		int pid = 0;

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

		put_state(cur_state);
	}

 end:
 aborted:
	state_dprintf("---------------------------------\n");

	trace_summary();

	mpi_async_stop(&sendq);
	mpi_async_stop(&recvq);
}

int main(int argc, char *argv[])
{
	MPI_Init(&argc, &argv);
	MPI_Comm_size(MPI_COMM_WORLD, &node_count);
	MPI_Comm_rank(MPI_COMM_WORLD, &node_id);

#ifdef DEBUG
	--node_count;
	debug_node = node_count;
	if (node_id == debug_node)
		debug_logger();
#endif

	mpi_dprintf("MPI node (%d of %d) starting...\n", node_id, node_count);

	dfs();

	return MPI_Finalize();
}
