set terminal jpeg

set key left top

set xlabel "n"
set ylabel "time"
set title "Plot for orb vs Runnable code, size pAdd"

set grid ytics lt 0 lw 1 lc rgb "#bbbbbb"
set grid xtics lt 0 lw 1 lc rgb "#bbbbbb"

set output "results/orbVsActualpAdd10.jpg"
plot \
"results/orbpAdd.data" using 1:2 t'orb' with linespoints, \
"results/opspAdd.data" using 1:2 t'oper' with linespoints, 
