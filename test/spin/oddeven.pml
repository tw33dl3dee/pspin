/*
 */

unsigned x : 31 = 2

active proctype Counter() {
  atomic {
	do
	  :: x < 10000000 -> x++
	  :: break
	od
  };

end:
  do
	:: x > 1 && x%2 -> x = 3*x + 1
	:: x%2 == 0 -> x = x/2
  od
}

active proctype Checker() {
  x == 1
}

