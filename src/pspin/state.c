/**
 * @file   state.c
 * @author Ivan Korotkov <twee@tweedle-dee.org>
 * @date   Mon Dec 28 19:37:08 2009
 * 
 * @brief  
 * 
 * 
 */

#include <assert.h>

#include "config.h"
#include "state.h"
#include "debug.h"
#include "bfs.h"

/** 
 * @brief Initialize transition tables
 * @return Head of transition table
 */
transitions_t init_transitions(void)
{
	transitions_t transitions;

#define TRANSITIONS_INIT
#include STATEGEN_FILE
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
static struct State *alloc_state(size_t svsize, int zero)
{
	struct State *state; 
	//state_dprintf(" (alloc new state of size %d) ", svsize);
	state = BFS_ALLOC(svsize);
	if (state != NULL) {
		if (zero)
			memset(state, 0, svsize);
		STATESIZE(state) = svsize;
	}
	return state;
}

/** 
 * @brief Initializes process state substructure
 * 
 * @param current Newly allocated process structure
 * @param proctype Proctype (is saved to `current')
 * @param pid Pid of new process
 */
static void init_process(struct Process *current, int proctype, int pid)
{
	PROCTYPE(current) = proctype;
	PROCIP(current) = 0;

#define PROCSTATE_INIT
#include STATEGEN_FILE
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
#include STATEGEN_FILE
#undef  STATE_INIT

	int pid = 0;
	proc = FIRST_PROC(state);
	for (int ptype = 0; ptype < NPROCTYPE; ++ptype)
		for (int i = 0; i < procactive[ptype]; ++i, ++pid) {
			init_process(proc, ptype, pid);
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
		COPY_STATE(new_state, state);
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
static struct State *copy_state_add_process(const struct State *state, int proctype)
{
	assert(proctype < NPROCTYPE);
	struct State *new_state = alloc_state(STATESIZE(state) + procsizes[proctype], 0);
	if (new_state != NULL) {
		memcpy(new_state, state, STATESIZE(state));
		/** 
		 * @bug 0 is passed instead of pid
		 */
		init_process(PROC_BY_OFFSET(new_state, STATESIZE(state)), proctype, 0);
	}
	return new_state;
}

/**
 * If non-zero, current process is inside d_step block
 */
static int in_dstep = 0;

/**
 * If non-zero, printf() output from PROMELA goes to stderr
 */
int use_pml_printf;

/** 
 * @brief Perform transition, if possible.
 *
 * If transition results in entering d_step context, calls itself
 * recursively until exiting out of it. 
 * 
 * @param transitions Matrix of transition relation (used for recursive calls)
 * @param pid Pid of current process
 * @param dest_ip IP to transition process to
 * @param state Current state
 * @param current Current process state
 * @param next_state Next state is stored here if transition passes
 * 
 * @return
 *  - [TransitionBlocked]     -- transition blocked
 *  - [TransitionPassed]      -- transition passed
 *  - [TransitionCausedAbort] -- transition passed and caused abort
 */
enum TransitionResult 
do_transition(transitions_t transitions, 
              int pid, int dest_ip,
              struct State *state, struct Process *current, 
              struct State **next_state)
{
	int current_offset, aborted = TransitionPassed;

	/* Hidden variables are static locals here
	 */

#define HIDDEN_VAR_DECL
#include STATEGEN_FILE
#undef  HIDDEN_VAR_DECL

#define RECORD_STEP(msg)									\
	state_dprintf(" PASSED\n");								\
	state_dprintf("Performing step: <<< %s >>>\n", msg);
#define CHECK_ALLOC(ptr)								\
	if (ptr == NULL) {									\
	    eprintf(ERROR_COLOR("==OUT OF MEMORY") "\n");	\
		return TransitionCausedAbort;					\
	}
#define NEW_STATE()											\
	if (!in_dstep) {										\
	    *next_state = copy_state(state);					\
		current_offset = PROC_OFFSET(current, state);		\
		state = *next_state;								\
		CHECK_ALLOC(state);									\
		current = PROC_BY_OFFSET(state, current_offset);	\
	}
#define NEW_STATE_NEW_PROC(proctype)							\
	if (!in_dstep) {											\
		*next_state = copy_state_add_process(state, proctype);	\
		current_offset = PROC_OFFSET(current, state);			\
		state = *next_state;									\
		CHECK_ALLOC(state);										\
		current = PROC_BY_OFFSET(state, current__offset);		\
	}
#define ASSERT(expr, repr)									\
	if (!(expr)) {											\
		eprintf(ERROR_COLOR("==ASSERTION VIOLATED:") " %s "	\
		        INFO_COLOR("IN PROCESS") " %d "				\
		        INFO_COLOR("IP") " %d -> %d\n",				\
		        repr, pid, current->_ip, dest_ip);			\
		edump_state(state);									\
		aborted = TransitionCausedAbort;					\
	}
#define BEGIN_ATOMIC() STATEATOMIC(state) = pid
#define END_ATOMIC()   STATEATOMIC(state) = -1
#define BEGIN_DSTEP() in_dstep = 1
#define END_DSTEP() in_dstep = 0

#ifdef DEBUG
#	define PRINTF(fmt, args...)					\
	printf("%d\n", use_pml_printf);				\
	state_dprintf("*** " fmt, ##args);
#else
#	define PRINTF(fmt, args...)					\
	if (use_pml_printf)							\
		eprintf("*** " fmt, ##args)
#endif

#define C_CODE_DEF
#include STATEGEN_FILE
#undef  C_CODE_DEF

#define TRANSITIONS
#include STATEGEN_FILE
#undef  TRANSITIONS

#define C_CODE_UNDEF
#include STATEGEN_FILE
#undef  C_CODE_UNDEF

  passed:
	PROCIP(current) = dest_ip;
	if (STATEATOMIC(state) >= 0)
		state_dprintf("ATOMIC now\n");

	/* If current process is in d_step context,
	 * make further transitions until it exits d_step
	 */
	if (aborted == TransitionPassed && in_dstep) {
		FOREACH_TRANSITION(transitions, current, src_ip, dest_ip) {
			state_dprintf("D\t%d -> %d ", src_ip, dest_ip);
			/* We can safely pass NULL, because no further states can be created here
			 */
			aborted = do_transition(transitions, pid, dest_ip, state, current, NULL);
			/* If not TransitionBlocked, d_step has reached it's end
			 */
			if (aborted != TransitionBlocked)
				return aborted;
		}

		eprintf(ERROR_COLOR("==BLOCKED IN D_STEP: ")
		        INFO_COLOR("IN PROCESS") " %d " 
		        INFO_COLOR("IP") " %d -> %d\n",
		        pid, current->_ip, dest_ip);
		edump_state(state);
		return TransitionCausedAbort;
	}

	return aborted;

  blocked:
	state_dprintf(" BLOCKED\n");
	return TransitionBlocked;
}

#define VALID_ENDSTATES
#include STATEGEN_FILE
#undef  VALID_ENDSTATES

/** 
 * @brief Check if state is a valid endstate.
 *
 * All processes must be blocked at theirs valid endstate IPs for check to pass.
 * If state is not actually endstate (i.e. some processes are executable), result undefined.
 * 
 * @param state State to check
 * 
 * @return 0 if check passed (valid endstate), -1 otherwise.
 */
int
check_endstate(struct State *state)
{
	FOREACH_PROCESS(state, 1) {
		for (int i = 0; valid_endstates[PROCTYPE(current)][i] != -1; ++i)
			if (valid_endstates[PROCTYPE(current)][i] == PROCIP(current))
				goto next_proc;
		goto invalid;
	  next_proc:
		continue;
	}

	return 0;

  invalid:
	eprintf(ERROR_COLOR("==INVALID END STATE:") "\n");
	edump_state(state);
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
#include STATEGEN_FILE
#undef  STATE_DUMP

	dump_dprintf("-\tHASH:      " HASH_FMT "\n", STATE_HASH(state, 0));

	int pid = 0;
	FOREACH_PROCESS(state, ++pid) {
		dump_dprintf("\t-Process %d:\n", pid);
#define PROCSTATE_DUMP
#include STATEGEN_FILE
#undef  PROCSTATE_DUMP
	}
}

/** 
 * @brief Dumps global and per-process state variables to error stream
 * 
 * @param state State to dump
 */
void edump_state(struct State *state) 
{
#define STATE_EDUMP
#include STATEGEN_FILE
#undef  STATE_EDUMP

	int pid = 0;
	FOREACH_PROCESS(state, ++pid) {
		eprintf("\t-Process %d:\n", pid);
#define PROCSTATE_EDUMP
#include STATEGEN_FILE
#undef  PROCSTATE_EDUMP
	}

	eprintf("-------------------------------------------------------\n");
}

/** 
 * @brief Dumps state bytes in hexadecimal view
 * 
 * @param state State to dump
 */
void hexdump_state(struct State *state) 
{
	unsigned char *data = (unsigned char *)state;

	dump_dprintf("(%d)<%02X", STATESIZE(state), data[0]);
	for (int i = 1; i < STATESIZE(state); ++i)
		dump_dprintf(" %02X", data[i]);
	dump_dprintf(">");
}
