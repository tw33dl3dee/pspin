/*
 * Configuration
 * *************** */
#define LOSS   0	/* enable or disable message loss */
#define QSZ	   5	/* length of message queues */
/* *************** */

chan sender	= [QSZ] of { byte, byte };
chan recv	= [QSZ] of { byte, byte };

#define RDY 100
#define NOTRDY 101
#define DATA 200
#define NODATA 201
#define RESET 1

active proctype Sender()
{
	short n = -1; byte t,m;
	
I:		/* Idle State */
	do
#if LOSS==1
  :: sender?_,_ -> progress2: skip
#endif
  :: sender?RESET,0 ->
ackreset:recv!RESET,0;	/* stay in idle */
	 n = -1;
	 goto I

	 /* E-rep: protocol error */

  :: sender?RDY,m ->		/* E-exp */
	 assert(m == (n+1)%4);
advance:n = (n+1)%4;
	 if
	  /* buffer */		:: atomic {
		  printf("MSC: NEW\n");
		  recv!DATA,n;
		  goto E
	  }
						   /* no buffer */		:: recv!NODATA,n;
												   goto N
	 fi

  :: sender?NOTRDY,m ->	/* N-exp */
expected:assert(m == (n+1)%4);
	 goto I

	 /* Timeout */
	 /* ignored (p.154, in [Needham'82]) */

  :: goto reset	/* spontaneous reset */
	 od;
E:		/* Essential element sent, ack expected */
	 do
#if LOSS==1
  :: sender?_,_ -> progress0: skip
#endif
  :: sender?RESET,0 ->
	 goto ackreset

  :: sender?RDY,m ->
	 if
	  :: (m == n) ->		/* E-rep */
		 goto retrans
	  :: (m == (n+1)%4) ->	/* E-exp */
		 goto advance
	 fi

  :: sender?NOTRDY,m ->	/* N-exp */
	 goto expected

	 /* Timeout */
	 /* a proper behaved timeout leaves part of the
		   protocol specification unreachable;	to check
		   less well-behaved timeout behavior, replace
		   the timeout keyword below with "empty(sender)"
		   to allow the retransmission at any time when the
		   sender queue is empty.  even more mis-behaved
		   timeouts can be checked by replacing timeout with
		   "skip"  (i.e., unconditionally executable)
	 */
  :: timeout ->
	 printf("MSC: STO\n");
retrans:recv!DATA,n	/* retransmit */

  :: goto reset
	  od;
N:		/* Non-essential element sent */
	  do
#if LOSS==1
  :: sender?_,_ -> progress1: skip
#endif
  :: sender?RESET,0 ->
	 goto ackreset

  :: sender?RDY,m ->		/* E-rep */
	 assert(m == n)		/* E-exp: protocol error */
	 -> recv!NODATA,n	/* retransmit and stay in N */

  :: recv!DATA,n;		/* buffer ready event */
	 goto E

  :: goto reset

	 /* Timeout */
	 /* ignored (p.154, in [Needham'82]) */
	   od;

reset:	recv!RESET,0;
	   do
#if LOSS==1
  :: sender?_,_ -> progress3: skip
#endif
  :: sender?t,m ->
	 if
	  :: t == RESET -> n = -1; goto I
	  :: else	/* ignored, p. 152 */
	 fi
  :: timeout ->
	 goto reset
		od
		}
active proctype Receiver()
{
	byte t, n, m, Nexp;

I:		/* Idle State */
	do
#if LOSS==1
  :: recv?_,_ -> progress2: skip
#endif
  :: recv?RESET,0 ->
ackreset:sender!RESET,0;		/* stay in idle */
	 n = 0; Nexp = 0;
	 goto I

  :: atomic { recv?DATA(m) ->	/* E-exp */
			  assert(m == n);
advance:		printf("MSC: EXP\n");
			  n = (n+1)%4;
			  assert(m == Nexp);
			  Nexp = (m+1)%4;
			  if
			   :: sender!RDY,n; goto E
			   :: sender!NOTRDY,n; goto N
			  fi
  }

  :: recv?NODATA(m) ->		/* N-exp */
	 assert(m == n)

	 /* Timeout: ignored */

	 /* only the receiver can initiate a data
		   transfer; p. 156 [Needham'82]
		   this is modeled by the statement below:
	 */
  :: empty(recv) -> sender!RDY,n; goto E

  :: goto reset
	 od;
E:	 
	 do
#if LOSS==1
  :: recv?_,_ -> progress1: skip
#endif
  :: recv?RESET,0 ->
	 goto ackreset

  :: atomic { recv?DATA(m) ->
			  if
			   :: ((m+1)%4 == n) ->		/* E-rep */
				  printf("MSC: REP\n");
				  goto retrans
			   :: (m == n) ->			/* E-exp */
				  goto advance
			  fi
  }

  :: recv?NODATA(m) ->		/* N-exp  */
	 assert(m == n);
	 goto I

	 /* see also the matching code in the sender model;
		   to check less well-behaved timeout behavior for
		   the receiver process, replace the timeout keyword
		   below with "empty(recv)" (or "skip" for a real
		   torture test, with significant extra complexity)
	 */
  :: timeout ->
	 printf("MSC: RTO\n");
retrans:sender!RDY,n;
	 goto E

  :: goto reset
	  od;
N:	  
	  do
#if LOSS==1
  :: recv?_,_ -> progress0: skip
#endif
  :: recv?RESET,0 ->
	 goto ackreset

  :: recv?DATA(m) ->		/* E-rep */
	 assert((m+1)%4 == n);	/* E-exp and N-exp: error */
	 printf("MSC: REP\n");
	 sender!NOTRDY,n	/* retransmit and stay in N */

  :: sender!RDY,n ->		/* buffer ready event */
	 goto E

	 /* Timeout: ignored */

  :: goto reset
	   od;
progress:
reset:	sender!RESET,0;
	   do
#if LOSS==1
  :: recv?_,_ -> progress3: skip
#endif
  :: recv?t,m ->
	 if
	  :: t == RESET -> n = 0; Nexp = 0; goto I
	  :: else	/* ignored, p. 152 */
	 fi
  :: timeout ->
	 goto reset
		od
		}
