/*
 */

#define N 100

chan chan1[N];
chan chan2[N];

proctype fib_r(int n)
{
	if
	 :: (n == 0) -> chan2[n]!1
					
	 :: (n == 1) -> run fib_r(n - 1);
					chan2[n]!1;
					chan1[n-1]!1
					
	 :: (n >= 2) -> int r, r1, r2;
					chan ch1 = [1] of { int };
					chan ch2 = [1] of { int };
					chan1[n-2] = ch1;
					chan2[n-2] = ch2;
					run fib_r(n - 1);
					ch1?r1;
					ch2?r2;
					r = r1 + r2;
					chan2[n]!r;
					chan1[n-1]!r;
	fi
}

proctype fib(int n; chan p)
{
	chan ch1 = [1] of { int };
	chan ch2 = [2] of { int };
	chan1[n-1] = ch1;
	chan2[n-1] = ch2;
	chan2[n] = ch2;

	int result;
	run fib_r(n);
	ch1?result;
	p!result;
}

init
{
	chan child = [1] of { int };
	int result;
	int n = 5;
	
	run fib(n, child);
	child?result;
	printf("fib(%d) = %d\n", n, result)
}
