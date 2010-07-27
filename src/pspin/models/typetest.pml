typedef MyType {
	byte x;
	byte y
}

chan ch = [1] of {MyType};

active proctype A() {
	MyType a;
	a.x = 1;

	ch ! a;
	
	skip
}
