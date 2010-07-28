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
		if (now.y > 6) {
			now.y = 9;
		}
	};
	assert(x == 4 && y == 3 || x == 8 && y == 9);
	if
	 :: c_code [(now.x) == 4] { now.y = 100; }
	 :: else
	fi;
	skip;
	assert(x == 4 && y == 100 || x == 8 && y == 9);
	do
	 :: c_expr (now.x < 9) -> x++
	 :: else -> break
	od;
	assert(x == 9);
}
