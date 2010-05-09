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

#define N 4							/* nr of processes */
#define L N							/* size of buffer (>= 2*N) */

byte nr_leaders = 0					/* count the number of process that
									 *	think they are leader of the ring */

CHAN(0)
CHAN(1)
CHAN(2)
CHAN(3)
/* CHAN(4) */
/* CHAN(5) */
/* CHAN(6) */
/* CHAN(7) */
/* CHAN(8) */
/* CHAN(9) */

PROC(0,1)
PROC(1,2)
PROC(2,3)
PROC(3,0)
/* PROC(4,0) */
/* PROC(5,6) */
/* PROC(6,7) */
/* PROC(7,0) */
/* PROC(8,9) */
/* PROC(9,0) */
