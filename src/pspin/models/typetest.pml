typedef MyType {
	byte x;
	byte y;
	byte z[3]
}

typedef MyType2 {
	MyType a[2]
}

chan ch = [1] of {MyType};

active proctype A() {
	MyType a;
	MyType b[2];

	MyType2 c[2];
	
	a.x = 1;
	b[0].y = 2;
	b[1].x = 3;

	//b[1].z[2] = 3;

	ch ! a;
	
	skip
}
