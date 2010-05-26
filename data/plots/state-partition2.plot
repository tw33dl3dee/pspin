set terminal postscript enhanced portrait font "Helvetica, 8pt" dashlength 3

set encoding koi8r
set output "state-partition2.eps"

set multiplot

set origin 0.0, 0.0
set size 0.8, 0.33

set key off

#set xrange [-1 : 7]
set yrange [0 : 100]
set y2range [0 : ]
set ytics  10 nomirror 
set y2tics 10 nomirror

set title "1 proc"

set xtics ("Election" 1, "Philo" 5)

set ylabel "%" rotate by 0
set y2label "Время (сек)"
set format y2 "%3.0f"

set tmargin 2
set bmargin 2

plot 'state-partition2-1.dat' using ($1*4+0):(100*$2):(1) with boxes title "Сообщения" fs pattern 1 lc rgb "#9C0E0E", 'state-partition2-1.dat' using ($1*4+1):(100*$3):(1)  with boxes title "Неравномерность распределения" fs pattern 4 ls 1 lc rgb "#0057AE", 'state-partition2-1.dat' using ($1*4+2):5:(1) axes x1y2 with boxes title "Время выполнения" fs solid 0.2 ls 1 lc rgb "#648000", 'state-partition2-1.dat' using ($1*4+2):4:(1) axes x1y2 with boxes title "Время простоя" fs solid 0.5 ls 1 lc rgb "#648000"

set origin 0.0, 0.33

set title "2 proc"

plot 'state-partition2-2.dat' using ($1*4+0):(100*$2):(1) with boxes title "Сообщений при переходах, %" fs pattern 1 lc rgb "#9C0E0E", 'state-partition2-2.dat' using ($1*4+1):(100*$3):(1)  with boxes title "Неравномерность распределения, %" fs pattern 4 ls 1 lc rgb "#0057AE", 'state-partition2-2.dat' using ($1*4+2):5:(1) axes x1y2 with boxes title "Время выполнения" fs solid 0.2 ls 1 lc rgb "#648000", 'state-partition2-2.dat' using ($1*4+2):4:(1) axes x1y2 with boxes title "Время простоя" fs solid 0.5 ls 1 lc rgb "#648000"

set origin 0.0, 0.66

set key left top

set title "Full"

plot 'state-partition2-full.dat' using ($1*4+0):(100*$2):(1) with boxes title "Сообщений при переходах, %" fs pattern 1 lc rgb "#9C0E0E", 'state-partition2-full.dat' using ($1*4+1):(100*$3):(1)  with boxes title "Неравномерность распределения, %" fs pattern 4 ls 1 lc rgb "#0057AE", 'state-partition2-full.dat' using ($1*4+2):5:(1) axes x1y2 with boxes title "Время выполнения" fs solid 0.2 ls 1 lc rgb "#648000", 'state-partition2-full.dat' using ($1*4+2):4:(1) axes x1y2 with boxes title "Время простоя" fs solid 0.5 ls 1 lc rgb "#648000"

