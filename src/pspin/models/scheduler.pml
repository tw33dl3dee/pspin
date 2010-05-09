mtype = {Wakeme, Running};

bit lk, sleep_q;
bit r_lock, r_want;
mtype State = Running;

active proctype client()
{
sleep:
	/* the sleep routine */
	atomic { (lk == 0) -> lk = 1};		/* SPINlock(&lk) */
	do									/* while r.lock is set */
	 :: (r_lock == 1) ->				/* r.lock == 1 */
		r_want = 1;						/* set the want flag */
		State = Wakeme;					/* remember State */
		lk = 0;							/* freelock(&lk) */
		(State == Running);				/* wait for wakeup */
	 :: else ->							/* r.lock == 0 */
		break
	od;

progress:								/* progress label */
	assert(r_lock == 0);				/* should still be true */
	r_lock = 1;							/* consumed resource */
	lk = 0;								/* freelock(&lk) */
	goto sleep
}

active proctype server()				/* interrupt routine */
{
wakeup:									/* wakeup routine */
	r_lock = 0;							/* r.lock = 0 */
	(lk == 0);							/* waitlock(&lk) */
	if
	 :: r_want ->						/* someone is sleeping */
		atomic {							/* get spinlock on sleep queue */
			(sleep_q == 0) -> sleep_q = 1
		};
		r_want = 0;						/* reset the want flag */
#ifdef PROPOSED_FIX
		(lk == 0);						/* waitlock(&lk) */
#endif
		if
		 :: (State == Wakeme) ->		/* the client process is asleep */
			State = Running;			/* wake-up the client process */
		 :: else -> skip
		fi;
		sleep_q = 0						/* release spinlock on sleep queue */
	 :: else -> skip
	fi;
	goto wakeup							/* jump to the wakeup label */
}
