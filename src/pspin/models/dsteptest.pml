int x = 0

active proctype p1() {
	if
	 :: x = 1
	 :: x = 2
	fi;
	d_step {
		do 
		 :: x < 100 -> x++;
			if
			 :: x == 10 -> x = 90
			 :: else
			fi;
		 :: break
		od;
	};
}

active proctype p2() {
	x > 2 -> assert(x == 100);
}
