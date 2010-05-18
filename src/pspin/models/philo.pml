/*
 * Configuration
 * ***************** */
#define PHILO_LR   3
#define PHILO_RL   0
#define PHILO_RETR 0
/* ***************** */

#define N (PHILO_LR + PHILO_RL + PHILO_RETR)

#define LFORK fork[_pid]
#define RFORK fork[(_pid + 1)%N]

#define ATE eaten_acc = eaten_acc + 1 - eaten[_pid]; eaten[_pid] = 1

byte fork[N]
byte nr_eat
byte eaten[N]
byte eaten_acc

active [PHILO_LR] proctype PhiloLR() {
Think:
	atomic { LFORK == 0 -> LFORK = 1 };
One:
	atomic { RFORK == 0 -> RFORK = 1; nr_eat++; ATE };
Eat:
	atomic { nr_eat--; RFORK = 0 };
	LFORK = 0;
	goto Think;
}

active [PHILO_RL] proctype PhiloRL() {
Think:
	atomic { RFORK == 0 -> RFORK = 1 };
One:
	atomic { LFORK == 0 -> LFORK = 1; nr_eat++; ATE };
Eat:
	atomic { nr_eat--; LFORK = 0 };
	RFORK = 0;
	goto Think;
}

active [PHILO_RETR] proctype PhiloRetr() {
Think:
	atomic { LFORK == 0 -> LFORK = 1; };
	/* assert(nr_eat == 0); */
One:
	if
	 :: atomic { RFORK == 0 -> RFORK = 1; nr_eat++; ATE }
	 :: atomic { RFORK != 0 -> LFORK = 0 }; goto Think
	fi;
Eat:
	atomic { nr_eat--; RFORK = 0; };
	LFORK = 0;
	goto Think
}

active proctype Checker() {
	eaten_acc = N;
}
