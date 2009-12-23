/* RIP */

mtype = {update};

typedef RipEntry {
  byte next;	/* next hop router name ('x', 'y', ...) */
  byte hops;	/* max hops via router (16 is infinite) */
}

/** @arg r Current entry
 *  @arg e Received entry
 *  @arg sf Entry to be sent forth
 *  @arg sb Entry to be sent back
 */
#ifdef POISON
#define UPDATE_ENTRY(r, e, sf, sb)														\
d_step {																				\
  if																					\
	:: e.hops < r.hops -> r.next = e.next; r.hops = e.hops;								\
						  sf.hops = r.hops + 1; sb.hops = 16;							\
	:: else																				\
  fi;																					\
}
#else
#define UPDATE_ENTRY(r, e, sf, sb)														\
d_step {																				\
  if																					\
	:: e.hops < r.hops -> r.next = e.next; r.hops = e.hops;								\
						  sf.hops = r.hops + 1											\
	:: else																				\
  fi;																					\
}
#endif

#define SEND_ENTRY(net, s)																\
  if																					\
    :: net!update(s)																	\
    :: skip  /* loose */																\
  fi

/* Networks */

/** Full-duplexing via pair of channels **/
#define RIP_NETWORK(name) chan net1_##name = [1] of {mtype, RipEntry}; chan net2_##name = [1] of {mtype, RipEntry};

/* Routers */

/** one network-connected router */
proctype Router1(chan net1in, net1out; byte name)
{
  RipEntry r, s, e;
#ifdef POISON
  RipEntry sp;
#else
# define sp s
#endif

  d_step {
	r.next = name;
	r.hops = (name == 'x' -> 1 : 16);
	s.next = name;
	sp.next = name;
	s.hops = 2;  /* used only for initial route */
  };

  /* [x] has initial route to (A) */
  if
	:: name == 'x' -> net1out!update(s)
	:: else
  fi;

end:
  do
	:: net1in?update(e) -> UPDATE_ENTRY(r, e, s, sp);
						   SEND_ENTRY(net1out, sp)
	:: /* EXPIRE */ r.hops = 16
  od
}

/** two networks-connected router */
proctype Router2(chan net1in, net1out, net2in, net2out; byte name)
{
  RipEntry r, s, e;
#ifdef POISON
  RipEntry sp;
#else
# define sp s
#endif

  d_step {
	r.next = name;
	r.hops = 16;
	s.next = name;
	sp.next = name;
  };

end:
  do
	:: net1in?update(e) -> UPDATE_ENTRY(r, e, s, sp); assert(!LOOP);
						   SEND_ENTRY(net1out, sp); SEND_ENTRY(net2out, s)
	:: net2in?update(e) -> UPDATE_ENTRY(r, e, s, sp); assert(!LOOP);
						   SEND_ENTRY(net1out, s); SEND_ENTRY(net2out, sp)
	:: /* EXPIRE */ r.hops = 16
  od;
}

/** three networks-connected router */
proctype Router3(chan net1in, net1out, net2in, net2out, net3in, net3out; byte name)
{
  RipEntry r, s, e;
#ifdef POISON
  RipEntry sp;
#else
# define sp s
#endif

  d_step {
	r.next = name;
	r.hops = 16;
	s.next = name;
	sp.next = name;
  };

end:
  do
	:: net1in?update(e) -> UPDATE_ENTRY(r, e, s, sp); assert(!LOOP);
						   SEND_ENTRY(net1out, sp); SEND_ENTRY(net2out, s); SEND_ENTRY(net3out, s)
	:: net2in?update(e) -> UPDATE_ENTRY(r, e, s, sp); assert(!LOOP);
						   SEND_ENTRY(net1out, s); SEND_ENTRY(net2out, sp); SEND_ENTRY(net3out, s)
	:: net3in?update(e) -> UPDATE_ENTRY(r, e, s, sp); assert(!LOOP);
						   SEND_ENTRY(net1out, s); SEND_ENTRY(net2out, s); SEND_ENTRY(net3out, sp)
	:: /* EXPIRE */ r.hops = 16
  od;
}
