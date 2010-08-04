chan ch = [2] of {int, byte}

active proctype A() {
	int x;
	byte y;
	
	ch?x,y;
	printf("X: %d, Y: %d\n", x, y);

	ch?x,y;
	printf("X: %d, Y: %d\n", x, y);

	ch?x,y;
	printf("X: %d, Y: %d\n", x, y);

	ch?x,y;
}

active proctype B() {
	ch!1,2;
	ch!2,3;
	ch!4,5;
}
