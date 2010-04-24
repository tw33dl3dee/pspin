bit fork[3]
byte nr_eat

active [3] proctype Philosopher() {
Think:
	atomic { fork[_pid] == 0 -> fork[_pid] = 1 };
One:
	atomic { fork[(_pid + 1)%3] == 0 -> fork[(_pid + 1)%3] = 1; nr_eat++ };
Eat:
	atomic { nr_eat--; fork[(_pid + 1)%3] = 0 };
	fork[_pid] = 0;
	goto Think
}

proctype Phil_another() {
Think:
	atomic { fork[(_pid + 1)%3] == 0 -> fork[(_pid + 1)%3] = 1 };
One:
	atomic { fork[_pid] == 0 -> fork[_pid] = 1; nr_eat++ };
Eat:
	atomic { nr_eat--; fork[_pid] = 0 };
	fork[(_pid + 1)%3] = 0;
	goto Think
}

proctype Phil_restart() {
Think:
	atomic { fork[_pid] == 0 -> fork[_pid] = 1; };
One:
	if
	 :: atomic { fork[(_pid + 1)%3] == 0 -> fork[(_pid + 1)%3] = 1; nr_eat++ }
	 :: atomic { fork[(_pid + 1)%3] != 0 -> fork[_pid] = 0 }; goto Think
	fi;
Eat:
	atomic { nr_eat--; fork[(_pid + 1)%3] = 0; };
	fork[_pid] = 0;
	goto Think
}
