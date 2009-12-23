/* Topology: (A) <-> [x] <-> (B) <-> [y] <-> (C) <-> [z] */

#define POISON

#define LOOP (r.next == 'y' && name == 'x')

#include "rip.pml"

/*RIP_NETWORK(A)*/ /* not used actually */
RIP_NETWORK(B)
RIP_NETWORK(C)

init {
  atomic {
  	run Router1(net1_B, net2_B, 'x');
  	run Router2(net2_B, net1_B, net1_C, net2_C, 'y');
  	run Router1(net2_C, net1_C, 'z')
  }
}
