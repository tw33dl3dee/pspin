/*
 * Fibonacci numbers.
 */

proctype fib2_r(int n; chan o1, o2, p)
{
	if
	 :: (n == 0) -> o1!1
					
	 :: (n == 1) -> run fib2_r(n - 1, p, p, p);
					o1!1; o2!1
					
	 :: (n >= 2) -> int r, r1, r2;
					chan i1 = [1] of { int };
					chan i2 = [1] of { int };
					run fib2_r(n - 1, i1, p, i2);
					i1?r1; i2?r2;
					r = r1 + r2;
					o1!r; o2!r
	fi
}

proctype fib2(int n; chan p)
{
	chan t = [2] of { int };
	run fib2_r(n, p, t, t);
}

init
{
	chan child = [1] of { int };
	int result;
	int n = 6;
	
	run fib2(n, child);
	child?result;
	printf("fib(%d) = %d\n", n, result)
}
