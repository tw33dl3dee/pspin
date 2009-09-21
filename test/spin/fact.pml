/*
 */

#define N 100

chan chan1[N];
chan chan2[N];

proctype fact(int n; chan p)
{
	chan child = [1] of { int };
	chans[n] = child;
	int result;
	
	if
	 :: (n <= 1) -> p!1
	 :: (n >= 2) ->
		run fact(n-1, chans[n]);
		child?result;
		p!n*result
	fi
}

init
{
	chan child = [1] of { int };
	int result;
	
	run fact(10, child);
	child?result;
	printf("result: %d\n", result)
}
