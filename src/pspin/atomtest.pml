int x = 0

active proctype Run1() {
  do
	:: atomic { x == 0 -> x = x + 1 }
	:: atomic { x == 1 -> x = x - 1 }
  od
}

active proctype Run2() {
  do
	:: atomic { x == 0 -> x = x + 2 }
	:: atomic { x == 2 -> x = x - 2 }
  od
}

active proctype Checker() {
  (x > 2) || (x < 0) -> assert(0)
}