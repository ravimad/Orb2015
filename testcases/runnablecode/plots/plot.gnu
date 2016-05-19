set terminal jpeg

set key left top

set xlabel "n"
set ylabel "alloc"
set title "Plot for Orb vs Runnable code"

set grid ytics lt 0 lw 1 lc rgb "#bbbbbb"
set grid xtics lt 0 lw 1 lc rgb "#bbbbbb"

set output "orbVsActual10.jpg"
plot \
"<(sed -n '1,20p' orb.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '1,20p' oper.data)" using 1:2 t'oper' with linespoints, 

set output "orbVsActual100.jpg"
plot \
"<(sed -n '20,40p' orb.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '20,40p' oper.data)" using 1:2 t'oper' with linespoints,

set output "orbVsActual1000.jpg"
plot \
"<(sed -n '40,50p' orb.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '40,50p' oper.data)" using 1:2 t'oper' with linespoints, 


