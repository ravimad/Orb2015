set terminal jpeg

set key left top

set xlabel "n"
set ylabel "time"
set title "Plot for inst vs Runnable code, size gennext"

set grid ytics lt 0 lw 1 lc rgb "#bbbbbb"
set grid xtics lt 0 lw 1 lc rgb "#bbbbbb"

set output "results/instVsActualgennext10.jpg"
plot \
"results/instgennext.data)" using 1:2 t'inst' with linespoints, \
"results/opsgennext.data)" using 1:2 t'oper' with linespoints, 
