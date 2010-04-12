int x = 2

active proctype Counter() {
	do
	 :: x < 10000 -> x++
	 :: break
	od;

	printf("COUNTER: %d\n", x);
	
	do
	 :: x%2      -> x = 3*x + 1
	 :: x%2 == 0 -> x = x/2
	od
}

active proctype Checker() {
	x == 1;
	assert(x != 1);
}
