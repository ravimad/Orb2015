## Artifact for the paper "Contract-based Resource Verification for Higher-order Functions with Memoization" 
Last Update: 12 Oct 2016, 14:30 CET: [Added a minor tip for low configuration machines](#runbench)

Virtual disk image containing the artifact: [popl-paper-184-artifact.tar.gz](http://lara.epfl.ch/~kandhada/popl-artifact/popl-paper-184-artifact.tar.gz) [md5](http://lara.epfl.ch/~kandhada/popl-artifact/popl-paper-184-artifact.md5) 

The above vdi image is pre-installed with the following artifacts:

1. The sources and executables of the resource verification system (Leon/Orb) described in the paper.
2. Sources of all benchmarks used in the evaluation.
3. All results and data used in the evaluation and presented in Figures 9 and 10 of the paper. 

Below we provide instructions for running our resource verification system (Leon/Orb) on the benchmarks, and 
for reproducing the results of the paper. Our tool can also be tried online on some benchmarks
at [leondev.epfl.ch](http://leondev.epfl.ch) (Memresource section). 
To know more about our tool and for getting started on writing and verifying new programs with Leon/Orb
please refer to the documentation [http://leondev.epfl.ch/doc/resourcebounds.html](http://leondev.epfl.ch/doc/resourcebounds.html).

## Booting the virtual disk image

1. Install [Oracle Virtual Box](https://www.virtualbox.org/wiki/Downloads). 
2. Extract the .vdi file from the archive.
3. Create a new virtual machine with the downloaded .vdi file as the hard disk. Our benchmarks are compute intensive. **The application needs at least 4GB of RAM and 2 processing cores for the virtual machine. Also, the host machine should have same or better configuration.** 
(Some benchmarks could timeout on lower configurations.)
4. When started, the virtual machine should boot Xubuntu 16.04 Linux operating system and will automatically log into the account : *popl* (password: *popl*)

## Running the tool on individual source files

The following command can be used to run individual source files. However, to reproduce the results presented in the paper we recommend using the scripts described in the subsequent sections.

    $ cd ~/leon
    $ ./leon --mem --benchmark --timeout=<secs> path-to-file

E.g. try `./leon --mem --benchmark --timeout=60 ./testcases/benchmarks/steps/LazySelectionSort.scala`.
The tool prints some log messages and the inferred bounds to the console. It dumps the final output and some statistics of the evaluation to a 
file \<filename\>-stats.txt in the directory from where the tool was run.
For a short description of the command line options use `leon --help`.
    
## <a name="runbench"></a> Running the tool on all benchmarks - Reproducing the results shown in Figure 9

As shown in the Figure 9 of the paper, a total of 17 benchmarks are used in the evaluation. Each benchmark has two versions: one with a `steps` bound, which denotes the number evaluation steps, and another with an `alloc` resource bound, which denotes the number of heap-allocated objects. The versions can be found in `~/leon/testcases/benchmark/steps` and `~/leon/testcases/benchmark/alloc` respectively.
Each benchmark has a brief description or pointers to the algorithm that is implemented.
The results of running the tool on these benchmarks are available in the folders inside the directory: `~/leon/results/`. 
The folder `~/leon/results/server-results` has the results of running the benchmarks on a server with the 
configurations presented in the paper, and provides more accurate data for the time taken by the tool to analyze a benchmark.

To infer the `steps` bounds of the benchmarks (shown in Figure 9), use the following commands:

    $ cd ~/leon/results
    $ mkdir steps; cd steps
    $ ../../scripts/steps.sh

To infer the `alloc` bounds of the benchmarks, replace `steps` by `alloc` in the above commands. The script may take few tens of minutes 
(depending on the VM configuration) to verify all benchmarks. **For slower machines it is possible to comment out some larger benchmarks
from the scripts.** The benchmarks `LazyNumericalRep.scala` and `Conqueue.scala` are among the largest and most time-consuming of all.

#### Understanding the output of the tool 

Running the script produces two files for each benchmark: `<benchmarkname>-stats.txt` and `<benchmarkname>.out`. The `*-stats` file provides several statistics in the form of _key : value_ pairs and has the  bounds inferred for every function (that has a template) in the benchmark. Note that the Figure 9 of the paper shows only the bounds inferred for a couple of selected functions in each benchmark (for each resource), whereas `*-stats` displays every bound inferred.  Below we list the functions in each benchmark whose bounds were presented in Figure 9. Reviewers may restrict their attention to these functions in all of the results that follow.

#### Key functions for each benchmark

1. LazySelectionSort - `kthMin` 
2. PrimeStream - `PrimesUntilN`
3. Fibonacci Stream - `nthFib`
4. Hamming Stream - `nthHammingNumber`
5. StreamLibrary - `isPrefixOf`
6. RealTimeQueue - `enqueue`, `dequeue`
7. Bottom-up merge-sort - `kthMin`
8. Deque- `cons`, `tail` and `reverse`
9. LazyNumericalRep - `incAndPay`
10. Conqueue - `pushLeftAndPay` and `concatNonEmpty`
11. LongestCommonSubsequence (LCS) - `lcsSols`
12. LevenshteinDistance - `levDistSols`
13. HammingMemoized - `hammingList`
14. WeightedScheduling - `schedBU`
15. Knapsack - `knapsack`
16. PackratParsing - `parse`
17. Viterbi - `viterbiSols`

#### Description of the Stats file

At the end of each stats file there are two tables: **Resource Verification Summary** and **State Verification Summary**.
The former table shows the inferred bounds for every function (including those presented in Figure 9), and the latter table  shows the result of verifying the correctness invariants needed for proving the resource bounds, which may possibly depend on the state of memoization. 
All the invariants in all the benchmarks will be verified by the tool and would be marked as **valid**. 
The table also shows the SMT solver among CVC4 and Z3 that succeeded first in deciding the generated verification conditions. 

Most of the key-value pairs in the stats file present details on the internals of the algorithm. The most relevant entries among these are 
_Total-Time_ (The column AT of Figure 9), _State-Verification-Time_ and _Resource-Verification-Time_.

#### Minor variances from Figure 9 results

Even though the tool makes a best effort to enforce determinism, minor variances across different runs (although rare) is possible. 
This is because of the incompleteness of the minimization problem in the presence of nonlinearity and recursive functions, 
and the non-determinism in SMT solvers. This means that occasionally the constants inferred by the tool may slightly vary 
compared to the ones presented in Figure 9. We observed a difference greater than +/- 1 in the inferred constants only in the two benchmarks: 
_PackratParsing_ and _Deque_ (for  the `steps` resource). 
In both cases the tool computed a more precise bound than the one presented in Figure 9, as the algorithm was able to 
perform more minimization.

## Measuring the accuracy of the inferred bounds - Reproducing the results shown in Figure 10

To measure the accuracy of the inferred bounds, we instrument the benchmarks to track the resources 
(using `./leon --instrument` option), and add drivers to run the benchmarks with inputs that exercise the worst-case behavior. 
All such instrumented benchmarks (having an executable `main` function) can be found in the folder: 
`~/leon/RuntimeEvaluation/src/main/scala/steps` (or alloc).  
The `main` function of an instrumented benchmarks invokes the _key functions_  on several inputs, 
computes the dynamic resource usage, and 
compares it against the statically inferred bounds as described in the section 5 of the paper. 
Use the following commands to run the instrumented benchmarks.

    $ cd ~/leon/RuntimeEvaluation/
    $ sbt                            
    
Once inside the `sbt` (Scala build tool) console, use the following command

    > run
    
The `run` command will list all the available benchmarks that can be executed. 
Choose the benchmark to run by entering its index. 
Running a benchmark will produce a set of `.data` and `.report` files in the directory: 
`~/leon/RuntimeEvaluation/results/steps/<Benchmarkname>/` (`steps` can be replaced by `alloc`). 
The content of these files are described shortly.

To compute the summary statistics shown in Figure 10, run the `StatsCollector` program (listed first) 
from the `sbt` console, which outputs the averages shown in Figure 10 to a file 
`~/leon/RuntimeEvaluation/Figure-10-data`. 

## Outputs of the instrumented benchmark

Running an instrumented benchmark outputs the following files in the directory: `~/leon/RuntimeEvaluation/results/steps/<Benchmarkname>/`:

1. `dynamic<benchmark-tag>.data`
2. `paretoanalysis<benchmark-tag>.report`
3.  One or more `pareto<index><benchmark-tag>.data`

Each `.data` file contains a list of triples: (a) the size (or another measure) of the input, 
(b) the statically inferred bound for the input, (c) the dynamic resource usage or 
the pareto optimal resource usage. For example, the file `dynamicmsort.data` has the following entries

    1000 57318 54546
    2000 113426 108612
    3000 169534 162656
    4000 225534 216678
    5000 281642 270722
    6000 337642 324722
    7000 393642 378744
    8000 449642 432744
    9000 505750 486788
    10000 561750 540788

The first line of the file indicates that for an input of size 1000, the statically inferred steps count was 
57318 and the runtime steps count was 54546. 
Using these data for each benchmark, the program `StatsCollector` computes a summary statistics using the formula 
shown in page 10 of the paper. 
This quantity, referred to as _dynamic/static * 100_, is outputted by `StatsCollector` (for each benchmark and resource) 
to the file `~/leon/RuntimeEvaluation/Figure-10-data`.

#### Comparisons with pareto optimal bounds

As explained in the section 5 of the paper, we also compare the statically inferred bounds to a set of  pareto optimal bounds 
with respect to the dynamic execution. 
Each pareto optimal bound is obtained by reducing a coefficient in the inferred bound, while preserving the other coefficients, 
until the bound is violated by a concrete input. 
The file `paretoanalysis<benchmark-tag>.report` reports the pareto optimal bound for each benchmark. 
For instance, the file `paretoanalysishams.report` (in folder `~/leon/RuntimeEvaluation/results/steps/CyclicHammingStream/`) 
has the following content:
    
    Statically inferred formula: 129*n + 4

    Reducing coeff 0 starting from 4
    Lowest possible value for the coefficient is 4
    Pareto optimal template: 129*n + 4
    First counter-example for 129*n + 3 is at the point 0

    Reducing coeff 1 starting from 129
    Lowest possible value for the coefficient is 124
    Pareto optimal template: 124*n + 4
    First counter-example for 123*n + 4 is at the point 8000

As explained in the report, for this benchmark, the first coefficient cannot be reduced any further, 
and the second coefficient could at best be reduced to 124 (without increasing the other coefficients) for the given dynamic runs. 
It shows that the data point 8000 violates the bound if the coefficient is reduced to 123.

The files `pareto0hams.data` and `pareto1hams.data` displays the statically inferred bound against the first and the second 
pareto optimal bound (respectively), for each input. 

Using these data for each benchmark, the program `StatsCollector` computes the metric _optimal/static * 100_ (for each benchmark and resource) 
and outputs it to the file `~/leon/RuntimeEvaluation/Figure-10-data`.

#### Minor variances from Figure 10 results

Even though most of the percentages in the `Figure-10-data` file are identical to the data shown in Figure 10 
of the paper, in a few benchmarks there is a slight difference (approximately 1 to 2 percentage) from the data 
shown in Figure 10. This is because, the results in the paper are more exhaustive and includes more top-level functions, 
whose evaluations require more complex drivers and manual effort. 
E.g. For the ease of artifact evaluation, the instrumented _BottomUpMergeSort_ benchmark provided fixes 
the value of `k` to a constant and only varies the size of the `input` (see Figure 9 for the bound of `kthMin`). 
However, in the results presented in the paper, `k` is also varied. The exact data used in the paper are also provided 
in the directory `~/leon/RuntimeEvaluation/results/archives/`.

#### Supplementary Graphs 

We have also provided some graphical plots of selected functions of the benchmarks to visualize the relationship between 
the dynamic resource usage and the statically inferred bounds 
in the folder: `~/leon/RuntimeEvaluation/results/graphs/`. 
The graphs `PackratParsing-pAdd` and `deque-rotateDrop` helps visualize the behavior of inner functions, 
which was summarized in Figure 11 of the paper.
The lines in the graphs denote the statically inferred bounds and the dots denote the runtime resource usage.

