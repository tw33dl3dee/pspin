bool want[2];	/* Bool array b */
bool turn;	/* integer    k */

proctype P(bool i)
{
  	want[i] = 1;
 	do
	 :: (turn != i) ->
  		(!want[1-i]);
 		turn = i
	 :: (turn == i) ->
 		break
 	od;
 	skip; /* critical section */
 	want[i] = 0
}

init { run P(0); run P(1) }
