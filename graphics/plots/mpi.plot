set terminal postscript enhanced landscape font "Helvetica, 16pt" dashlength 3

set encoding koi8r
set output "mpi.eps"

set xlabel "Размер сообщения (байт)"
set ylabel "Время (мксек)"

set xtics 0,128,1024
set xrange [ 0 : 1200 ]

set key

set multiplot
set origin 0.0,0.0
set size 1.0,1.0

plot 'mpi-sync.dat' using 4:5 title "Send/Recv" with lines , 'mpi-async.dat' using 4:5 title "Isend/Irecv" with lines lt 4, 'mpi-putpscw.dat' using 4:5 title "active RMA" with linespoints pt 8 ps 1 lt 2, 'mpi-putlock.dat' using 4:5 title "passive RMA" with linespoints pt 2 ps 1 lt 2

set origin 0.57,0.39
set size 0.42,0.28
set xrange [ 0 : 384 ] 
set yrange [ 5 : 8 ]
set xlabel ""
set ylabel ""
set ytics (5,6,7)
set xtics (128,256)
set key off

plot 'mpi-sync.dat' using 4:5 title "Send/Recv" with lines , 'mpi-async.dat' using 4:5 title "Isend/Irecv" with lines lt 4
