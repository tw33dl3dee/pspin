#define N 6

byte turn[N], flag[N]
byte ncrit

active [N] proctype User()
{
	byte j, k;
	
again:
	k = 0;

loop:
	flag[_pid] = k;
	turn[k] = _pid;
	
	j = 0;
	do
	 :: j == _pid ->
		j++
	 :: j != _pid ->
		if
		 :: j < N ->
			(flag[j] < k || turn[k] != _pid);
			j++
		 :: j >= N ->
			break
		fi
	od;

	if
	 :: k+1 < N -> goto loop
	 :: else -> k++
	fi;

	ncrit++;
	assert(ncrit == 1);
	ncrit--;
	
	flag[_pid] = 0;
	goto again
}
