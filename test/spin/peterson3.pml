byte turn[3], flag[3]
byte ncrit

active [3] proctype user()
{
  byte j, k;

again:
  k = 0;
  do
	:: k < 3 -1 ->
	   flag[_pid] = k;
	   turn[k] = _pid;

	   j = 0;
	   do
		 :: j == _pid ->
			j++
		 :: j != _pid ->
			if
			  :: j < 3 ->
				 (flag[j] < k || turn[k] != _pid);
				 j++
			  :: j >= 3 ->
				 break
			fi
	   od;
	   k++
	:: else ->
	   break
  od;

  ncrit++;
  assert(ncrit == 1);
  ncrit--;

  flag[_pid] = 0;
  goto again
}
