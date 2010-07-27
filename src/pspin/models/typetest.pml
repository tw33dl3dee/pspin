typedef MyType {
	byte x;
	byte y
}

active proctype A() {
	MyType a;
	a.x = 1;
	skip
}
