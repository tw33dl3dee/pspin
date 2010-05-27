set terminal postscript enhanced landscape font "Helvetica, 8pt" dashlength 3

set encoding koi8r
set output "state-partition1.eps"

set multiplot

set origin 0.0, 0.0
set size 0.5, 0.5

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

set tmargin 2
set bmargin 2

plot 'state-partition1-philo.dat' using ($1*4+0):(100*$2):(1) with boxes title "Сообщения" fs pattern 1 lc rgb "#9C0E0E", 'state-partition1-philo.dat' using ($1*4+1):(100*$3):(1)  with boxes title "Неравномерность распределения" fs pattern 4 ls 1 lc rgb "#0057AE", 'state-partition1-philo.dat' using ($1*4+2):5:(1) axes x1y2 with boxes title "Время выполнения" fs solid 0.2 ls 1 lc rgb "#648000", 'state-partition1-philo.dat' using ($1*4+2):4:(1) axes x1y2 with boxes title "Время простоя" fs solid 0.5 ls 1 lc rgb "#648000"

set origin 0.0, 0.5

set key left top

set title "Алгоритм выбора лидера"

plot 'state-partition1-election.dat' using ($1*4+0):(100*$2):(1) with boxes title "Сообщений при переходах, %" fs pattern 1 lc rgb "#9C0E0E", 'state-partition1-election.dat' using ($1*4+1):(100*$3):(1)  with boxes title "Неравномерность распределения, %" fs pattern 4 ls 1 lc rgb "#0057AE", 'state-partition1-election.dat' using ($1*4+2):5:(1) axes x1y2 with boxes title "Время выполнения" fs solid 0.2 ls 1 lc rgb "#648000", 'state-partition1-election.dat' using ($1*4+2):4:(1) axes x1y2 with boxes title "Время простоя" fs solid 0.5 ls 1 lc rgb "#648000"

