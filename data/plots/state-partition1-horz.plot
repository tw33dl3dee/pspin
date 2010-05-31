set terminal postscript enhanced landscape font "Helvetica, 16pt" dashlength 3

set encoding koi8r
set output "state-partition1-horz.eps"

set key off

set xrange [-1 : 11]
set yrange [0 : 100]
set y2range [0 : ]
set ytics  10 nomirror 
set y2tics 10 nomirror

set title "Философы"

set xtics ("По 1 процессу" 1, "По 2 процессам" 5, "По всему состоянию" 9)

set ylabel "%" rotate by 0
set y2label "Время (сек)"
set format y2 "%3.0f"

plot 'state-partition1-horz-philo.dat' using ($1*4+0):(100*$2):(1) with boxes notitle fs pattern 1 lc rgb "#9C0E0E", 'state-partition1-horz-philo.dat' using ($1*4+1):(100*$3+1):(1)  with boxes notitle fs pattern 4 ls 1 lc rgb "#0057AE", 'state-partition1-horz-philo.dat' using ($1*4+2):5:(1) axes x1y2 with boxes notitle fs solid 0.2 ls 1 lc rgb "#648000", 'state-partition1-horz-philo.dat' using ($1*4+2):4:(1) axes x1y2 with boxes notitle fs solid 0.5 ls 1 lc rgb "#648000"

set key left top

set ylabel ""
set y2label ""

set size 1, 1
set origin -0.05, 0.1

set title "Выборы лидера"

plot 'state-partition1-horz-election.dat' using ($1*4+0):(100*$2):(1) with boxes title "Доля сообщений среди переходов {/Symbol t}, %" fs pattern 1 lc rgb "#9C0E0E", 'state-partition1-horz-election.dat' using ($1*4+1):(100*$3+1):(1)  with boxes title "Неравномерность распределения {/Symbol x}, %" fs pattern 4 ls 1 lc rgb "#0057AE", 'state-partition1-horz-election.dat' using ($1*4+2):5:(1) axes x1y2 with boxes title "Время выполнения, сек" fs solid 0.2 ls 1 lc rgb "#648000", 'state-partition1-horz-election.dat' using ($1*4+2):4:(1) axes x1y2 with boxes title "Время простоя, сек" fs solid 0.5 ls 1 lc rgb "#648000"

