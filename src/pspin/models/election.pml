#define N 8					/* nr of processes */
#define I 3					/* node given the smallest number */
#define L 16				/* size of buffer (>= 2*N) */

mtype = {one, two, winner}; /* three symbolic msg names */

chan q[N] = [L] of {mtype, byte};	/* asynchronous channel */

byte nr_leaders = 0;				/* count the number of process that
									 *	think they are leader of the ring */

proctype node(chan in, out; byte mynumber)
{
	bit Active = 1, know_winner = 0;
	byte nr, maximum = mynumber, neighbourR;

	out!one(mynumber);					/* send msg of type one, with par mynumber */
end:
	do
	 :: in?one(nr) ->					/* receive msg of type one, with par nr */
		if
		 :: Active ->
			if
			 :: nr != maximum ->
				out!two(nr);
				neighbourR = nr
			 :: else ->					/* max is greatest number */
				assert(nr == N);
				know_winner = 1;
				out!winner,nr;
			fi
		 :: else ->
			out!one(nr)
		fi
	 :: in?two(nr) ->
		if
		 :: Active ->
			if
			 :: neighbourR > nr && neighbourR > maximum ->
				maximum = neighbourR;
				out!one(neighbourR)
			 :: else ->
				Active = 0
			fi
		 :: else ->
			out!two(nr)
		fi
	 :: in?winner,nr ->
		if
		 :: nr != mynumber -> skip
		 :: else ->
			nr_leaders++;
			assert(nr_leaders == 1)
		fi;
		if
		 :: know_winner
		 :: else -> out!winner,nr
		fi;
		break
	od
}

init {
	byte proc;
	atomic {
		/* atomically activate N copies of proc template node */
		proc = 1;
		do
		 :: proc <= N ->
			run node (q[proc-1], q[proc%N], (N+I-proc)%N+1);
			proc++
		 :: proc > N ->
			break
		od
	}
}
