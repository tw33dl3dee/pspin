set terminal postscript enhanced landscape font "Helvetica, 16pt" dashlength 3

set encoding koi8r
set output "states-speed.eps"

set xlabel "Количество состояний"
set ylabel "Время (сек)"

set key left top
set logscale x
set logscale y

set style line 1 lt 1 lc rgb "#9C0E0E" pt 2
set style line 2 lt 1 lc rgb "#0057AE" pt 10
set style line 3 lt 2 lc rgb "#9C0E0E"
set style line 4 lt 1 lc rgb "#A02788" pt 6

plot 'states-speed-spin.dat' using 1:2 smooth bezier title "SPIN" with lines ls 1, 'states-speed-pspin.dat' using 1:2 smooth bezier title "Хэширование с коллизиями" with lines ls 2, 'states-speed-spin.dat' using 1:2 notitle with points ls 1, 'states-speed-pspin.dat' using 1:2 notitle with points ls 2, 'states-speed-spin-fail.dat' using 1:2 notitle with lines ls 3, 'states-speed-pspin-bithash.dat' using (200*$1):(200*$2) smooth bezier title "Битовое хэширование" with lines ls 4, 'states-speed-pspin-bithash.dat' using (200*$1):(200*$2) notitle with points ls 4
