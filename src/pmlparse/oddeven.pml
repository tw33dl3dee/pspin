# 1 "../../test/spin/oddeven.pml"
# 1 "<built-in>"
# 1 "<command-line>"
# 1 "../../test/spin/oddeven.pml"



int x = 100;

proctype A() {
  do
	:: x%2 -> x = 3*x + 1
  od
}

proctype B() {
  do
	:: x%2 == 0 -> x = x/2
  od
}

init {
  atomic {
	run A();
	run B();
  };
  assert(x != 1);
}
