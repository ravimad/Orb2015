set terminal jpeg

set key left top

set xlabel "n"
set ylabel "time"
set title "Plot for orb vs Runnable code, size LevenshteinDistance"

set grid ytics lt 0 lw 1 lc rgb "#bbbbbb"
set grid xtics lt 0 lw 1 lc rgb "#bbbbbb"

set output "results/orbVsActualLevenshteinDistance10.jpg"
plot \
"<(sed -n '1,20p' results/orbLevenshteinDistance.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '1,20p' results/opsLevenshteinDistance.data)" using 1:2 t'oper' with linespoints, 

set output "results/orbVsActualLevenshteinDistance100.jpg"
plot \
"<(sed -n '20,40p' results/orbLevenshteinDistance.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '20,40p' results/opsLevenshteinDistance.data)" using 1:2 t'oper' with linespoints,

set output "results/orbVsActualLevenshteinDistance1000.jpg"
plot \
"<(sed -n '40,50p' results/orbLevenshteinDistance.data)" using 1:2 t'orb' with linespoints, \
"<(sed -n '40,50p' results/opsLevenshteinDistance.data)" using 1:2 t'oper' with linespoints, 
