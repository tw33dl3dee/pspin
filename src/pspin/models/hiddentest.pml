byte x
hidden byte y

active proctype p1() {
	d_step {
		y = 1;
		x = y + 1;
	};
	assert(x == 2);
}
