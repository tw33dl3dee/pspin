/**
 * @file   parmpi.c
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Sun Mar 21 16:56:28 2010
 * 
 * @brief  Параллельная генерация состояний с использованием MPI.
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

#include "config.h"
#include "state.h"
#include "state_hash.h"
#include "bfs.h"
#include "mpi_async.h"
#include "mpi_tags.h"
#include "debug.h"

/**
 * Через сколько состояний печатать промежуточную статистику.
 */
#define STAT_THRESHOLD (10*1000*1000)

/**
 * Число узлов, за исключением узла журналирования.
 */
int node_count;
/**
 * Номер текущего узла.
 */
int node_id;

/**
 * Максимальный размер сообщения (не должен превышать максимально возможный размер состояния
 *                                либо счетчика сообщений)
 */
#define MAX_STATESIZE 1024
/**
 * Длина асинхронной MPI-очереди
 */
#define MPI_QLEN      32

/**
 * Индекс буфера, взятого последним из очереди приема.
 */
static int last_buf_no = -1;
/**
 * Очереди приема и отправки.
 */
static struct mpi_queue sendq, recvq;

/*
 * Статистика
 */

/**
 * Число локально хранимых состояний.
 */
static uint64_t state_count;
/**
 * Число выполненных переходов.
 */
static uint64_t trans_count;
/**
 * Число удаленных вызовов с новыми состояниями.
 */
static uint64_t state_msg_count;
/**
 * Число удаленных вызовов управляющего характера.
 */
static uint64_t ctrl_msg_count;
/**
 * Максимальная длина очереди поиска.
 */
static size_t max_bfs_len;
/**
 * Время запуска.
 */
static double start_time;

/** 
 * @brief Запись времени начала работы.
 */
static void trace_start()
{
	start_time = MPI_Wtime();
}

/** 
 * @brief Запись выборки нового сосотяния из очереди.
 */
static void trace_state_begin(struct State *state)
{
	state_count++;
}

/** 
 * @brief Запись внутреннего перехода.
 */
static void trace_state_new(struct State *state)
{
	if (BFS_CUR_LEN() > max_bfs_len)
		max_bfs_len = BFS_CUR_LEN();
	trans_count++;
}

/** 
 * @brief Запись удаленного вызова с новым состоянием.
 * 
 * @param node_idx Номер узла-назначения
 */
static void trace_state_send(struct State *state, int node_idx)
{
	state_msg_count++;
}

/** 
 * @brief Запись управляющего удаленного вызова.
 * 
 * @param node_idx Номер узла-назначения
 */
static void trace_ctrl_send(int node_idx)
{
	ctrl_msg_count++;
}

/** 
 * @brief Вывод результатов сбора статистики
 */
static void trace_summary()
{
	float total_time = MPI_Wtime() - start_time;
	float wait_time = recvq.wait_time + sendq.wait_time;
	float run_time = total_time - wait_time;

	iprintf("Parallel run summary:\n");

	iprintf("\tTime:\n");
	iprintf("\t\tTotal:         %.3f sec\n", 
	        total_time);
	iprintf("\t\tRun:           %.3f sec (%.1f%% total)\n", 
	        run_time, run_time*100./total_time);
	iprintf("\t\tIdle           %.3f sec (%.3f recv, %.3f send)\n",
	        wait_time, recvq.wait_time, sendq.wait_time);
	iprintf("\tTransitions taken: %.0f (%.1f/sec)\n",
	        (double)trans_count, trans_count/run_time);
	iprintf("\tMessages passed:   %.0f (%.2f%% trans), control: %.0f (%.2f%% all)\n",
	        (double)state_msg_count, state_msg_count*100./trans_count,
	        (double)ctrl_msg_count, ctrl_msg_count*100./(ctrl_msg_count + state_msg_count));
	iprintf("\tStates:            %.0f (%.1f/sec)\n",
	        (double)state_count, state_count/run_time);
	iprintf("\tBFS queue len:     %zd (%.2f%% states, %.2f%% trans)\n",
	        max_bfs_len, 
	        max_bfs_len*100./state_count, max_bfs_len*100./trans_count);

	state_hash_stats();

	iprintf("BRIEF S%.0f T%.0f M%.0f R%.3f I%.3f\n",
	        (double)state_count, (double)trans_count, (double)state_msg_count, run_time, wait_time);
}

/** 
 * @brief Вывод промежуточных результатов сбора статистики
 */
static void trace_inter_stat()
{
	double total_time = MPI_Wtime() - start_time;
	
	iprintf("Time: %.0f, states: %.0f, trans: %.0f ", 
	        total_time, (double)state_count, (double)trans_count);
	state_hash_inter_stats();
	iprintf("\n");
}

/**
 * Каждый узел и передаваемое сообщение-счетчик имеют цвет
 */
enum Color { Black = 0, White };

struct MsgCount {
	/**
	 * Счетчик сообщений.
	 */
	int count;
	/**
	 * Цвет счетчика.
	 */
	enum Color color;
};

/**
 * Счетчик и цвет текущего узла
 */
static struct MsgCount msg_counter = { .color = White };
/**
 * Пересылаемый счетчик и его цвет.
 * Цвет инициализируется черным, иначе нулевой узел посчитает работу завершенной в самом начале.
 */
static struct MsgCount msg_accum   = { .color = Black };
/**
 * Если не ноль, текущий узел является владельцем счетчика.
 */
static int has_accum;

/**
 * Узел, обнаруживший удаленное завершение (либо -1)
 */
static int termination_detected_id = -1;

/** 
 * @brief Обнаружение удаленного завершения
 * 
 * @param node Номер узла, обнаружившего завершение
 */
static void termination_detected(int node)
{
	if (node == node_id)
		mpi_dprintf("=== INITIATING TERMINATION ===\n");
	termination_detected_id = node;
}

/** 
 * @brief Рассылает всем остальным узлам уведомление о завершении
 */
static void announce_termination()
{
	mpi_dprintf("Announcing termination from node %d\n", termination_detected_id);
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
 * @brief Инициализация счетчиков сообщений
 *
 * В сущности просто помечает нулевой узел как держателя счетчика.
 */
static void init_msg_counter()
{
	if (node_id == 0)
		has_accum = 1;
}

/** 
 * @brief Пересылает счетчик сообщений следующему узлу.
 * 
 * Текущий узел должен быть держателем счетчика.
 * 
 * @param target_node Номер узла-назначения (обычно следующий узел)
 */
static void send_msg_counter(int target_node)
{
	msg_accum.count += msg_counter.count;

	/* If a black machine forwards the token, the token turns black */
	if (msg_counter.color == Black)
		msg_accum.color = Black;

	int buf_no = mpi_async_get_buf(&sendq, 0);
	memcpy(MPI_ASYNC_BUF(&sendq, buf_no, void), &msg_accum, sizeof(struct MsgCount));
	mpi_async_queue_buf(&sendq, buf_no, sizeof(struct MsgCount), MPI_CHAR, target_node, TagMsgCount);
	trace_ctrl_send(target_node);

	/* When a node forwards the token, the node turns white. */
	msg_counter.color = White;
	has_accum = 0;
}

/** 
 * @brief Проверка завершение, вызывается при неактивности узла.
 * 
 * Если текущий узел не является держателем счетчика, ничего не делает.
 * Если завершение не обнаружено, пересылает счетчик дальше.
 * 
 * @return -1 if termination detected, 0 otherwise.
 */
static int termination_check()
{
	if (!has_accum)
		return 0;

	/*
	 * Only 0'th node does termination detection, 
	 * others just forward token, updating it.
	 */
	if (node_id == 0) {
		/*
		 * When node 0 receives the token again, it can conclude termination, if 
		 * - node 0 is passive and white, 
		 * - the token is white, and it's value is 0
		 */
		if (msg_counter.color == White && msg_accum.color == White && msg_accum.count == 0) {
			termination_detected(node_id);
			return -1;
		}
		/* Otherwise, node 0 may start a new probe. */
		else {
			msg_accum.count = 0;
			msg_accum.color = White;
		}
	}

	send_msg_counter((node_id + 1)%node_count);
	
	return 0;
}

/** 
 * @brief Обработка принятого счетчика сообщений
 * 
 * @param new_accum Принятый счетчик и его цвет
 */
static void msg_count_accum(struct MsgCount *new_accum)
{
	msg_accum = *new_accum;
	has_accum = 1;
}

/** 
 * @brief Обновляет локальный счетчик сообщений после отправки
 */
static void msg_count_sent()
{
	msg_counter.count++;
}

/** 
 * @brief Обновляет локальный счетчик сообщений после приема
 */
static void msg_count_recv()
{
	msg_counter.count--;
	/* When a node receives a message, the node turns black. */
	msg_counter.color = Black;
}

/** 
 * @brief Добавление состояния в хэш-таблицу, если оно там не присутствует.
 * 
 * @param state Структура состояния
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
		msg_count_sent();
	}
	else 
		/*
		 * Local state;
		 * this will already push new state to BFS.
		 */
		state_hash_add(state, /* don't copy */ BfsAdd);
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
	struct MsgCount msg_accum;
	/**
	 * Message carries termination request.
	 * In this case, it contains number of node that detected termination.
	 * @sa TagTerminate
	 */
	int termination_originator;
};

/** 
 * @brief Освобождает буфер, занятый последним принятым сообщением.
 */
static void release_last_msg()
{
	mpi_dprintf("[RELEASE BUF %d]\n", last_buf_no);
	mpi_async_put_buf(&recvq, last_buf_no, MAX_STATESIZE, MPI_CHAR, MPI_ANY_SOURCE, MPI_ANY_TAG);
}

/** 
 * @brief Releases last state received by get_state().
 *
 * Releases buffer hold by state and updates message counters.
 * @attention sets last_buf_no to -1 so that subsequent calls do nothing.
 * 
 * @sa get_state
 * @sa release_last_msg
 */
static void put_state()
{
	if (last_buf_no != -1) {
		release_last_msg();
		last_buf_no = -1;
	}
}

/** 
 * @brief Processes incoming MPI message.
 * 
 * Classifies received messages and updates counters, if needed.
 * 
 * @param msg Message received
 * @param status MPI_Status of receive operation (contains message tag and source)
 * @param new_state Location to store pointer to new state to (defined only if return value is NewState)
 * 
 * @return Message classification
 */
static 
enum { 	
	NewState,					///< Message carries new state (already added to local hash, returned in *new_state)
	OldState,					///< Message carries old state (was present in hash, already released)
	NoState,					///< Message carries control data, poll further
	Terminate,					///< Message was a termination request, stop polling.
} process_msg(union Message *msg, const MPI_Status *status, struct State **new_state)
{
	int is_new;

	switch (status->MPI_TAG) {
	case TagTerminate:
		/* Termination detected by another node
		 */
		termination_detected(msg->termination_originator);
		return Terminate;

	case TagState:
		msg_count_recv();

#ifdef NETWORK_TO_LOCAL_QUEUE
		/*
		 * Copy state from MPI buffer to local statespace
		 */
		is_new = state_hash_add(&msg->state, /* copy */ BfsAddCopy);
		if (is_new) {
			*new_state = BFS_TAKE();
			put_state();
			return NewState;
		}
#else
		/*
		 * Use states directly in MPI buffer, don't release it 
		 */
		is_new = state_hash_add(&msg->state, /* don't copy nor add to BFS */ BfsNoAdd);
		if (is_new) {
			*new_state = &msg->state;
			return NewState;
		}
#endif
		/*
		 * MPI buffer with old state is released anyway
		 */
		put_state();
		return OldState;

	case TagMsgCount:
		msg_count_accum(&msg->msg_accum);
		release_last_msg();
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
 * State must be later released by calling put_state().
 * 
 * @return New state (already added to hash) or NULL, if termination detected and node should shut down.
 * 
 * @sa put_state
 */
static struct State *get_state(void)
{
	struct State *state;

	/*
	 * First check if there are incoming messages 
	 */
	for (;;) {
		last_buf_no = mpi_async_deque_buf(&recvq, 1);
		if (last_buf_no != -1) {
			switch (process_msg(MPI_ASYNC_BUF(&recvq, last_buf_no, union Message), 
			                    MPI_ASYNC_STATUS(&recvq, last_buf_no), &state)) {
			case NewState:	return state;
			case Terminate:	return NULL;
			default:		continue;
			}
		}
		else break;
	}

	/*
	 * Then check local queue 
	 */
	if ((state = BFS_TAKE()) != NULL)
		return state;

	/*
	 * Inactive: check if need to pass message counter to next node
	 */
	if (termination_check() < 0)
		return NULL;

	/*
	 * Block and wait for new messages 
	 */
	for (;;) {
		last_buf_no = mpi_async_deque_buf(&recvq, 0);
		switch (process_msg(MPI_ASYNC_BUF(&recvq, last_buf_no, union Message), 
		                    MPI_ASYNC_STATUS(&recvq, last_buf_no), &state)) {
		case NewState:	return state;
		case Terminate:	return NULL;
		default:		break;
		}
		
		/*
		 * Inactive: check if need to pass message counter to next node
		 */
		if (termination_check() < 0)
			return NULL;
	}
}

/** 
 * @brief Perform DFS search and build hash-table of all states
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

	init_msg_counter();

	state_dprintf("Initial state: ");
	init_state = create_init_state();
	queue_new_state(init_state);
	transitions = init_transitions();

	/* Until terminated */
	while ((cur_state = get_state()) != NULL) {
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
					termination_detected(node_id);
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
			if (check_endstate(cur_state) < 0) {
				termination_detected(node_id);
				goto aborted;
			}
		}
#endif

		state_dprintf("PUT STATE\n");
#ifndef NETWORK_TO_LOCAL_QUEUE
		/*
		 * No need to re-release buffer when states are copied to statespace
		 */
		put_state();
#endif

		if (state_count%STAT_THRESHOLD == 0)
			trace_inter_stat();
	}

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
