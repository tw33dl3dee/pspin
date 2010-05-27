/*
 * Configuration
 * ******************/
#define N 9							/* nr of processes */
#define L N							/* size of buffer (>= 2*N) */
/* ******************/

#define ONE 101
#define TWO 102
#define WINNER 200

#define CHAN(number)												\
chan q_##number = [L] of {byte, byte}

#define PROC(number, prev)														\
active proctype node_##number()													\
{																				\
	bit Active = 1, know_winner = 0;											\
	byte nr, maximum = MYNUMBER(_pid), neighbr, msg;							\
																				\
	q_##number!ONE(MYNUMBER(_pid));												\
																				\
	do																			\
	 :: q_##prev?msg,nr ->														\
		if																		\
		 :: msg == ONE && Active && nr != maximum ->							\
			q_##number!TWO(nr);													\
			neighbr = nr														\
		 :: msg == ONE && Active && nr == maximum ->							\
			know_winner = 1;													\
			q_##number!WINNER,nr;												\
		 :: msg == ONE && !Active ->											\
			q_##number!ONE(nr)													\
		 :: msg == TWO && Active && neighbr > nr && neighbr > maximum ->		\
			maximum = neighbr;													\
			q_##number!ONE(neighbr)												\
		 :: msg == TWO && Active && !(neighbr > nr && neighbr > maximum) ->		\
			Active = 0															\
		 :: msg == TWO && !Active ->											\
			q_##number!TWO(nr)													\
		 :: msg == WINNER ->													\
			if																	\
			 :: nr != MYNUMBER(_pid) -> skip									\
			 :: else ->															\
				nr_leaders++;													\
				assert(nr_leaders == 1)											\
			fi;																	\
			if																	\
			 :: know_winner														\
			 :: else -> q_##number!WINNER,nr									\
			fi;																	\
			break																\
		fi																		\
	od																			\
}

#define MYNUMBER(pid) (pid+1)

byte nr_leaders = 0					/* count the number of process that
									 *	think they are leader of the ring */

CHAN(0)
CHAN(1)
#if N > 2
CHAN(2)
#endif
#if N > 3
CHAN(3)
#endif
#if N > 4
CHAN(4)
#endif
#if N > 5
CHAN(5)
#endif
#if N > 6
CHAN(6)
#endif
#if N > 7
CHAN(7)
#endif
#if N > 8
CHAN(8)
#endif
#if N > 9
CHAN(9)
#endif

PROC(0,1)
#if N > 2
PROC(1,2)
#if N > 3
PROC(2,3)
#if N > 4
PROC(3,4)
#if N > 5
PROC(4,5)
#if N > 6
PROC(5,6)
#if N > 7
PROC(6,7)
#if N > 8
PROC(7,8)
#if N > 9
PROC(8,9)
PROC(9,0)
#else
PROC(8,0)
#endif
#else
PROC(7,0)
#endif
#else
PROC(6,0)
#endif
#else
PROC(5,0)
#endif
#else
PROC(4,0)
#endif
#else
PROC(3,0)
#endif
#else
PROC(2,0)
#endif
#else
PROC(1,0)
#endif
