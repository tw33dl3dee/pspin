bit fork[7]
byte nr_eat

active [7] proctype Philosopher() {
Think:
  atomic { fork[_pid] == 0 -> fork[_pid] = 1 };
One:
  atomic { fork[(_pid + 1)%7] == 0 -> fork[(_pid + 1)%7] = 1; nr_eat++ };
Eat:
  atomic { nr_eat--; fork[(_pid + 1)%7] = 0 };
  fork[_pid] = 0;
  goto Think
}

proctype Phil_another() {
Think:
  atomic { fork[(_pid + 1)%7] == 0 -> fork[(_pid + 1)%7] = 1 };
One:
  atomic { fork[_pid] == 0 -> fork[_pid] = 1; nr_eat++ };
Eat:
  atomic { nr_eat--; fork[_pid] = 0 };
  fork[(_pid + 1)%7] = 0;
  goto Think
}

proctype Phil_restart() {
Think:
  atomic { fork[_pid] == 0 -> fork[_pid] = 1; };
One:
  if
	:: atomic { fork[(_pid + 1)%7] == 0 -> fork[(_pid + 1)%7] = 1; nr_eat++ }
	:: atomic { fork[(_pid + 1)%7] != 0 -> fork[_pid] = 0 }; goto Think
  fi;
Eat:
  atomic { nr_eat--; fork[(_pid + 1)%7] = 0; };
  fork[_pid] = 0;
  goto Think
}
