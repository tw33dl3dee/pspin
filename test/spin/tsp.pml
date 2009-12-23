local bit vv[4];
local int cost;

c_state "int min_cost" "Hidden" "1000";

active proctype TSP()
{
P0:
  atomic {
	if
	  :: !vv[3] -> cost = cost + 2; goto P3;
	  :: !vv[1] -> cost = cost + 7; goto P1;
	  :: !vv[2] -> cost = cost + 9; goto P2;
	fi
  }

P1:
  atomic {
	vv[1] = true;
	if
	  :: !vv[2] -> cost = cost + 3; goto P2;
	  :: else   -> cost = cost + 4; goto end;
	  :: !vv[3] -> cost = cost + 7; goto P3;
	fi
  }

P2:
  atomic {
	vv[2] = true;
	if
	  :: !vv[1] -> cost = cost + 7; goto P1;
	  :: else   -> cost = cost + 6; goto end;
	  :: !vv[3] -> cost = cost + 8; goto P3;
	fi
  }

P3:
  atomic {
	vv[3] = true;
	if
	  :: else   -> cost = cost + 2; goto end;
	  :: !vv[1] -> cost = cost + 3; goto P1;
	  :: !vv[2] -> cost = cost + 8; goto P2
	fi
  }

end:
  c_code {
	if (now.cost < min_cost) {
	  min_cost = now.cost;
	  printf("found solution: %d\n", now.cost);
	  putrail();
	  Nr_Trails--;  /* save last trail */
	}
  }
}

#define higher_cost (c_expr { now.cost >= min_cost })

never {    /* <> higher_cost */
T0_init:
  if
	:: ((higher_cost)) -> goto accept_all
	:: (1) -> goto T0_init
  fi;
accept_all:
  skip
}
