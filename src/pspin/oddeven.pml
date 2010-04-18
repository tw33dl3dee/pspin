int y = 2;

active proctype Counter() {
	int x;

restart:
	x = y;

	printf("COUNTER: %d\n", x);
	
	do
	 :: x%2 && x > 1 -> x = 3*x + 1
	 :: x%2 == 0     -> x = x/2
	 :: else         -> break
	od;

	printf("REACHED 1, RESTART\n");

	y++;
	goto restart;
}

active proctype Checker() {
	y > 10;
	assert(0);
}
