/**
 * @file   parmpi.c
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Sun Mar 21 16:56:28 2010
 * 
 * @brief  Parallel statespace driver using MPI.
 * 
 */

#ifndef MPI
#	error "MPI macro must be defined in MPI version"
#endif

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

/**
 * Total number of nodes, except logger (if present).
 */
int node_count;
/**
 * Own number, 0-based.
 */
int node_id;

/**
 * Maximum size of MPI message (must not be less than maximum possible state size 
 *                              or counter array size)
 */
#define MAX_STATESIZE 1024
/**
 * Length of async MPI queue
 */
#define MPI_QLEN      32

/**
 * Number of last buffer dequeued from incoming queue.
 */
static int last_buf_no = -1;
/**
 * Incoming and outgoing queues.
 */
static struct mpi_queue sendq, recvq;

/*
 * Tracer data.
 */

/**
 * Number of states locally stored/processed.
 */
static int state_count;
/**
 * Number of transitions locally performed.
 */
static int trans_count;
/**
 * Number of remote calls carrying new states made.
 */
static int state_msg_count;
/**
 * Number of remote calls with control data made.
 */
static int ctrl_msg_count;
/**
 * Maximum BFS queue length in use.
 */
static int max_bfs_size;
/**
 * Start time of run.
 */
static double start_time;

/** 
 * @brief Record the start time.
 */
static void trace_start()
{
	start_time = MPI_Wtime();
}

/** 
 * @brief Record beginning of new state exploration.
 */
static void trace_state_begin(struct State *state)
{
	state_count++;
}

/** 
 * @brief Record performed transition (no matter if state is already in hash or not).
 */
static void trace_state_new(struct State *state)
{
	if (BFS_LEN() > max_bfs_size)
		max_bfs_size = BFS_LEN();
	trans_count++;
}

/** 
 * @brief Record outgoing remote call (MPI message) carrying new state.
 * 
 * @param node_idx Node to which the state is sent
 */
static void trace_state_send(struct State *state, int node_idx)
{
	state_msg_count++;
}

/** 
 * @brief Record outgoing remote call with control data (message counters, etc)
 * 
 * @param node_idx Node to which the state is sent
 */
static void trace_ctrl_send(int node_idx)
{
	ctrl_msg_count++;
}

/** 
 * @brief Output summary of recorded statistic
 */
static void trace_summary()
{
	float run_time = MPI_Wtime() - start_time;

	iprintf("Parallel run summary:\n");

	iprintf("\tTransitions taken: %d (%.1f/sec)\n",
			trans_count, trans_count/run_time);
	iprintf("\tMessages passed:   %d (%.2f%%)\n",
			state_msg_count, state_msg_count*100.f/trans_count);
	iprintf("\tStates:            %d (%.1f/sec)\n",
			state_count, state_count/run_time);
	iprintf("\tBFS max size:      %d (%.2f%% st, %.2f%% tr)\n",
			max_bfs_size, 
			max_bfs_size*100.f/state_count, max_bfs_size*100.f/trans_count);
}

/**
 * Array of message counters.
 * i-th element is number of messages sent to that node and not yet received.
 */
static int *msg_counters;

#define msg_counters_size (sizeof(msg_counters[0])*node_count)

/** 
 * @brief Prints out values of message counters
 */
static void print_msg_counters()
{
	mpi_dprintf("===Message counters: ");
	for (int i = 0; i < node_count; ++i) 
		mpi_dprintf("%d ", msg_counters[i]);
	mpi_dprintf("===\n");
}

/** 
 * @brief Initializers message counters array
 */
static void init_msg_counters()
{
	msg_counters = calloc(sizeof(msg_counters[0]), node_count);
}

/** 
 * @brief Sends message counters to another node
 * 
 * @param target_node Target node number
 */
static void send_msg_counters(int target_node)
{
	int buf_no = mpi_async_get_buf(&sendq, 0);
	memcpy(MPI_ASYNC_BUF(&sendq, buf_no, void), msg_counters, msg_counters_size);
	mpi_async_queue_buf(&sendq, buf_no, msg_counters_size, MPI_CHAR, target_node, TagMsgCount);
	trace_ctrl_send(target_node);
}

/** 
 * @brief Updates message counters with data received from another node
 * 
 * @param msg_count_accum Cumulative counters received
 * 
 * @return 0 if distributed system still running, -1 if termination has been detected.
 */
static int update_msg_counters(int msg_count_accum[])
{
	/* COUNT <- COUNT + ACCU */
	for (int i = 0; i < node_count; ++i)
		msg_counters[i] += msg_count_accum[i];
	print_msg_counters();
	/* if COUNT[j] <= 0 THEN */
	if (msg_counters[node_id] <= 0) {
		for (int i = 0; i < node_count; ++i)
			/* if COUNT != 0* */
			if (msg_counters[i] != 0) {
				/* send <COUNT> to Pj+1 */
				send_msg_counters((node_id + 1)%node_count);
				/* COUNT <- 0* */
				memset(msg_counters, 0, msg_counters_size);
				return 0;
			}
		/* if COUNT = 0* */
		return -1;
	}	
	return 0;
}

/** 
 * @brief Updates message counters after sending message to another node.
 * 
 * @param node Node to which message was sent
 */
static void msg_count_sent(int node)
{
	msg_counters[node]++;
	print_msg_counters();
}

/** 
 * @brief Updates message counters after received message has been processed.
 *
 * @return 0 if distributed system still running, -1 if termination has been detected.
 */
static int msg_count_recv()
{
	msg_counters[node_id]--;
	print_msg_counters();
	/* if COUNT[j] <= 0 THEN */
	if (!msg_counters[node_id]) {
		for (int i = 0; i < node_count; ++i)
			/* if COUNT != 0* */
			if (msg_counters[i] != 0) {
				/* send <COUNT> to Pj+1 */
				send_msg_counters((node_id + 1)%node_count);
				/* COUNT <- 0* */
				memset(msg_counters, 0, msg_counters_size);
				return 0;
			}
		/* if COUNT = 0* */
		return -1;
	}	
	return 0;	
}

/**
 * If non-negative, termination has been already detected by that node
 */
static int termination_detected_id = -1;

/** 
 * @brief Broadcasts termination order to all other nodes, including logger
 * 
 */
static void announce_termination()
{
	/*
	 * "Terminate" message consists of 1 (unused) INT with originator node number
	 */
	for (int node = 0; node < node_count; ++node) 
		if (node != node_id) {
			MPI_Send(&termination_detected_id, 1, MPI_INT, node, TagTerminate, MPI_COMM_WORLD);
			trace_ctrl_send(node);
		}
#ifdef DEBUG
	MPI_Send(&termination_detected_id, 1, MPI_INT, debug_node, TagTerminate, MPI_COMM_WORLD);
	trace_ctrl_send(debug_node);
#endif
}

/** 
 * @brief Checks if state is already in hash table, adds it otherwise.
 * 
 * @param state State structure
 */
static void queue_new_state(struct State *state)
{
	int state_node = STATE_NODE_IDX(state, node_count);

	mpi_dprintf("[Belongs to NODE %d] ", state_node);
	if (state_node != node_id) {
		/* State belongs to another node */
		int buf_no = mpi_async_get_buf(&sendq, 0);
		COPY_STATE(MPI_ASYNC_BUF(&sendq, buf_no, void), state);
		mpi_async_queue_buf(&sendq, buf_no, STATESIZE(state), MPI_CHAR, state_node, TagState);
		mpi_dprintf("[SENT]\n");
		trace_state_send(state, state_node);
		msg_count_sent(state_node);
	}
	else if (state_hash_add(state)) {
		/* Local state */
		state_dprintf(" - ADDED\n");
		BFS_ADD(state);
	}
}

/**
 * Union of all possible message data layouts.
 * Logging messages (`TagDebugLog') not included here.
 */
union Message {
	/**
	 * Message carries new state.
	 * @sa TagState
	 */
	struct State state;
	/**
	 * Message carries other node's message counters.
	 * @sa TagMsgCount
	 */
	int msg_count_accum[0];
	/**
	 * Message carries termination request.
	 * In this case, it contains number of node that detected termination.
	 * @sa TagTerminate
	 */
	int termination_originator;
};

/** 
 * @brief Processes incoming MPI message.
 * 
 * Classifies received messages and updates counters, if needed.
 * 
 * @param msg Message received
 * @param status MPI_Status of receive operation (contains message tag and source)
 * 
 * @return Message classification
 */
static 
enum { 	
	NewState,					///< Message carries new state (already added to local hash)
	NoState,					///< Message carries either old state or control data, poll further
	Terminate,					///< Message was a termination request, stop polling.
} process_msg(union Message *msg, const MPI_Status *status)
{
	switch (status->MPI_TAG) {
	case TagTerminate:
		/* Termination detected by another node
		 */
		termination_detected_id = msg->termination_originator;
		return Terminate;

	case TagState:
		return state_hash_add(&msg->state) ? NewState : NoState;

	case TagMsgCount:
		if (update_msg_counters(msg->msg_count_accum) < 0)
			return Terminate;
		else
			return NoState;
		
	default:
		printf("ERROR: unexpected message tag (%d)\n", status->MPI_TAG);
		assert(/* invalid message tag */ 0);
	}
}

/** 
 * @brief Gets next state to process.
 * 
 * First checks incoming queues, if any messages have been received;
 * then checks local BFS queue;
 * if both are negative, polls incoming queue for new messages.
 * 
 * @return New state (already added to hash) or NULL, if termination detected and node should shut down.
 */
static struct State *get_state(void)
{
	struct State *state;

	/*
	 * We detected termination just on last put_state() -- stop
	 */
	if (termination_detected_id >= 0)
		return NULL;

	/*
	 * First check if there are incoming messages 
	 * @todo Drain MPI queue into local queue instead of deque/put
	 */
	do {
		last_buf_no = mpi_async_deque_buf(&recvq, 1);
		if (last_buf_no != -1) {
			switch (process_msg(MPI_ASYNC_BUF(&recvq, last_buf_no, union Message), 
								MPI_ASYNC_STATUS(&recvq, last_buf_no))) {
			case NewState:
				return MPI_ASYNC_BUF(&recvq, last_buf_no, struct State);
			case Terminate:
				return NULL;
			case NoState:
				continue;
			}
		}
	} while (last_buf_no != -1);
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
		switch (process_msg(MPI_ASYNC_BUF(&recvq, last_buf_no, union Message), 
							MPI_ASYNC_STATUS(&recvq, last_buf_no))) {
		case NewState:
			return MPI_ASYNC_BUF(&recvq, last_buf_no, struct State);
		case Terminate:
			return NULL;
		case NoState:
			continue;
		}
	}
}

/** 
 * @brief Releases MPI buffer occupied by a received state.
 * 
 * @param state Processed state
 */
static void put_state(struct State *state)
{
	if (last_buf_no != -1) {
		mpi_dprintf("[RELEASE BUF %d]\n", last_buf_no);
		mpi_async_put_buf(&recvq, last_buf_no, MAX_STATESIZE, MPI_CHAR, MPI_ANY_SOURCE, MPI_ANY_TAG);
		if (msg_count_recv() < 0)
			/* We've detected termination.
			 * Next call to get_state() will return NULL and node will stop.
			 */
			termination_detected_id = node_id;
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
	init_msg_counters();

	state_dprintf("Initial state: ");
	init_state = create_init_state();
	queue_new_state(init_state);
	transitions = init_transitions();

	/* Until terminated */
	while ((cur_state = get_state()) != NULL) {
		int pid = 0;
		int transitions_possible = 0;

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
					++transitions_possible;

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

		if (!transitions_possible) {
			state_dprintf("End-state, performing validity check...\n");
			if (check_endstate(cur_state) < 0)
				goto aborted;
		}

		put_state(cur_state);
	}

 end:
 aborted:
	state_dprintf("---------------------------------\n");
	trace_summary();

	announce_termination();

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
	if (node_id == debug_node) {		
		debug_logger();
		return MPI_Finalize();
	}
#endif

	iprintf("MPI node (%d of %d) starting...\n", node_id, node_count);
	dfs();
	iprintf("MPI node (%d of %d) stopped\n", node_id, node_count);

	return MPI_Finalize();
}
