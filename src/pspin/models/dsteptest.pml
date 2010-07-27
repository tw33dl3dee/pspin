int x = 0

active proctype Run1() {
  do
	:: d_step { x == 0 -> x = x + 1 }
	:: d_step { x == 1 -> x = x - 1 }
  od
}

active proctype Run2() {
  do
	:: d_step { x == 0 -> x = x + 2 }
	:: d_step { x == 2 -> x = x - 2 }
  od
}

active proctype Checker() {
  (x > 2) || (x < 0) -> assert(0)
}
