byte n;

active proctype p1() {
	byte x;
	
	n = 1;
	atomic {
		do
		 :: n > 0 ->
			if
			 :: skip
			 :: skip -> break
			fi
		 :: n < 0 -> n++
		 :: n++ -> break
		od
	};
	n = 2;
	c_code <<{ this.n = 1;
			   Pp1->x = 2;
	}>>
}

active proctype p2() {
end:
	n = 1;

	if
	 :: n > 0 -> n = -1
	 :: n < 0 -> n = 1
	 :: else
	fi
}

active proctype p3() {
end:
	do
	 :: n > 0 -> n = -1
	 :: n < 0 -> n = 1
	od
}
