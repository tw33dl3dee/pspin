byte x
byte y

active proctype p1() {
	if
	 ::	x = 2
	 :: x = 3
	fi;
	c_code {
		now.x = 1 << now.x;
		now.y = now.x - 1;
	};
	assert(x == 4 || x == 8);
	assert(y == x - 1);
	if
	 :: c_code [now.x == 4] { now.y = 100; }
	 :: else
	fi;
	skip;
	assert(x == 4 && y == 100 || x == 8 && y == 7);
	do
	 :: c_expr (now.x < 9) -> x++
	 :: else -> break
	od;
	assert(x == 9);
}
