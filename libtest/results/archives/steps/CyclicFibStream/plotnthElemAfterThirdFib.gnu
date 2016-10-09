set terminal jpeg

set key left top

set xlabel "n"
set ylabel "time"
set title "Plot for orb vs Runnable code, size nthElemAfterThirdFib"

set grid ytics lt 0 lw 1 lc rgb "#bbbbbb"
set grid xtics lt 0 lw 1 lc rgb "#bbbbbb"

set output "results/orbVsActualnthElemAfterThirdFib10.jpg"
plot \
"<(sed -n '1,20p' results/orbnthElemAfterThirdFib.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '1,20p' results/opsnthElemAfterThirdFib.data)" using 1:2 t'oper' with linespoints, 

set output "results/orbVsActualnthElemAfterThirdFib100.jpg"
plot \
"<(sed -n '20,40p' results/orbnthElemAfterThirdFib.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '20,40p' results/opsnthElemAfterThirdFib.data)" using 1:2 t'oper' with linespoints,

set output "results/orbVsActualnthElemAfterThirdFib1000.jpg"
plot \
"<(sed -n '40,50p' results/orbnthElemAfterThirdFib.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '40,50p' results/opsnthElemAfterThirdFib.data)" using 1:2 t'oper' with linespoints, 
