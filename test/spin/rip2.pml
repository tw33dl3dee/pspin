/* Topology: (A) <-> [x] <-> (B) <-> [y] <-> (C) <-> [z]
 *                                    |               |
 *                                   (D) <-> [w] <-> (E)
 */

#define POISON

#define LOOP (name == 'x' && r.next == 'y' || name == 'y' && (r.next == 'z' || r.next == 'w'))

#include "rip.pml"

/*RIP_NETWORK(A)*/ /* not used actually */
RIP_NETWORK(B)
RIP_NETWORK(C)
RIP_NETWORK(D)
RIP_NETWORK(E)

init {
  atomic {
  	run Router1(net1_B, net2_B, 'x');
  	run Router3(net2_B, net1_B, net1_C, net2_C, net1_D, net2_D, 'y');
	run Router2(net2_C, net1_C, net1_E, net2_E, 'z');
  	run Router2(net2_D, net1_D, net2_E, net1_E, 'w');
  }
}
