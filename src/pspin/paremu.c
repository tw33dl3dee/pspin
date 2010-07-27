/**
 * @file   paremu.c
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Thu Feb 25 13:18:12 2010
 * 
 * @brief  Последовательная эмуляция параллельного выполнения.
 * 
 */

#ifdef MPI
#	error "MPI macro must not be defined in emulation version"
#endif

#include <assert.h>
#include <string.h>
#include <time.h>
#include <sys/time.h>
#include <getopt.h>

#include "config.h"
#include "state.h"
#include "state_hash.h"
#include "bfs.h"
#include "debug.h"

/**
 * Через сколько состояний печатать промежуточную статистику.
 */
#define STAT_THRESHOLD (10*1000*1000)

/**
 * Индекс "текущего" эмулируемого узла.
 */
static int cur_node_idx;
/**
 * Количество состояний на каждом узле.
 */
static uint64_t states_per_node[NODECOUNT];
/**
 * Суммарное число всех состояний.
 */
static uint64_t state_count;
/**
 * Суммарное число внутренних переходов.
 */
static uint64_t trans_count;
/**
 * Суммарное число удаленных вызовов.
 */
static uint64_t xnode_count;
/**
 * Максимальная длина очереди за время работы.
 */
static size_t max_bfs_len;
/**
 * Время запуска.
 */
static struct timeval start_time;

/** 
 * @brief Запись времени начала работы.
 */
static void trace_start()
{
	gettimeofday(&start_time, NULL);
}

/** 
 * @brief Запись выборки нового сосотяния из очереди.
 */
static void trace_state_begin(struct State *state)
{
	cur_node_idx = STATE_NODE_IDX(state, NODECOUNT);
	states_per_node[cur_node_idx]++;
	state_count++;
}

/** 
 * @brief Запись внутреннего перехода (и, возможно, удаленного вызова).
 */
static void trace_state_new(struct State *state)
{
	int node_idx = STATE_NODE_IDX(state, NODECOUNT);
	if (node_idx != cur_node_idx) {
		state_dprintf("Message: node %d --> node %d \n", cur_node_idx, node_idx);
		xnode_count++;
	}
	if (BFS_CUR_LEN() > max_bfs_len)
		max_bfs_len = BFS_CUR_LEN();
	trans_count++;
}

/** 
 * @brief Вывод результатов сбора статистики
 */
static void trace_summary()
{
	struct timeval end_time;
	gettimeofday(&end_time, NULL);

	double run_time = (end_time.tv_sec - start_time.tv_sec) + 
	    0.000001*(end_time.tv_usec - start_time.tv_usec);

	iprintf("Emulation summary:\n");

	iprintf("\tTransitions taken: %.0f (%.1f/sec)\n"
			"\tMessages passed:   %.0f (%.2f%% trans)\n",
			(double)trans_count, trans_count/run_time,
			(double)xnode_count, xnode_count*100./trans_count);

	iprintf("\tStates:\n"
			"\t\tTotal:   %.0f (%.1f/sec)\n",
			(double)state_count, state_count/run_time);
	
	uint64_t states_max = 0, states_min = states_per_node[0];
	for (int i = 0; i < NODECOUNT; ++i) {
		if (states_min > states_per_node[i])
			states_min = states_per_node[i];
		if (states_max < states_per_node[i])
			states_max = states_per_node[i];
		iprintf("\t\tNode %2d: %.0f (%.1f%%)\n",
				i, (double)states_per_node[i], states_per_node[i]*100./state_count);
	}
	iprintf("\t\tMin/max: %.2f\n", 
			states_min*1./states_max);

	iprintf("\tBFS queue len:     %zd (%.2f%% states, %.2f%% trans)\n",
			max_bfs_len, 
			max_bfs_len*100./state_count, max_bfs_len*100./trans_count);

	state_hash_stats();

	iprintf("BRIEF S%.0f T%.0f M%.0f R%.3f I%.3f\n",
	        (double)state_count, (double)trans_count, (double)xnode_count, run_time, 0.0);

	for (int i = 0; i < NODECOUNT; ++i) 
		iprintf("[%d] BRIEF S%.0f T%.0f M%.0f R%.3f I%.3f\n", 
		        i, (double)states_per_node[i], (double)trans_count/NODECOUNT, (double)xnode_count/NODECOUNT, run_time, 0.0);		
}

/** 
 * @brief Вывод промежуточных результатов сбора статистики
 */
static void trace_inter_stat()
{
	struct timeval end_time;
	gettimeofday(&end_time, NULL);

	double run_time = (end_time.tv_sec - start_time.tv_sec) + 
	    0.000001*(end_time.tv_usec - start_time.tv_usec);

	iprintf("[%.0f] States: %.0f, trans: %.0f ", 
	        run_time, (double)state_count, (double)trans_count);
	state_hash_inter_stats();
}

/** 
 * @brief Добавление состояния в хэш-таблицу, если оно там не присутствует.
 * 
 * @param state Структура состояния
 */
static void queue_new_state(struct State *state)
{
	/*
	 * This will already push new state to BFS.
	 */
	state_hash_add(state, /* don't copy */ BfsAdd);
}

/** 
 * @brief Поиск в ширину
 */
static void bfs(void)
{
	struct State *init_state;
	struct State *cur_state, *next_state;
	transitions_t transitions;

	BFS_INIT();

	trace_start();

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
					state_dprintf("TRANSITION: " HASH_FMT " => " HASH_FMT "\n",
					              STATE_HASH(cur_state, 0), STATE_HASH(next_state, 0));

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

		if (state_count%STAT_THRESHOLD == 0)
			trace_inter_stat();
	}

 aborted:
	state_dprintf("---------------------------------\n");

	trace_summary();
}

int main(int ac, char *av[])
{
	char c;

	opterr = 0;
	while ((c = getopt(ac, av, "d")) != -1)
		switch (c) {
		case 'd':
			dump_new_states = 1;
			break;

		default:
			abort();
		}
		
	bfs();

	return 0;
}
