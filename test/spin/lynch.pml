/*
 * Simple model-checking example.
 */

#define MIN	9
#define MAX	12
#define FILL	99

mtype = { ack, nak, err }

proctype transfer(chan chin, chout)
{
	byte o, i, last_i=MIN;
	
	o = MIN+1;
	do
	 :: chin?nak(i) ->
		assert(i == last_i+1);
		chout!ack(o)
	 :: chin?ack(i) ->
		if
		 :: (o <  MAX) -> o = o+1
		 :: (o >= MAX) -> o = FILL
		fi;
		chout!ack(o)
	 :: chin?err(i) ->
		chout!nak(o)
	od
}

proctype channel(chan in, out)
{
	byte md, mt;
	do
	 :: in?mt,md ->
		if
		 :: out!mt,md
		 :: out!err,0
		fi
	od
}

init
{
	chan AtoB = [1] of { mtype, byte };
	chan BtoC = [1] of { mtype, byte };
	chan CtoA = [1] of { mtype, byte };
	atomic {
		run transfer(AtoB, BtoC);
		run channel(BtoC, CtoA);
		run transfer(CtoA, AtoB)
	};
	AtoB!err,0;	/* start */
	0		/* hang */
}
