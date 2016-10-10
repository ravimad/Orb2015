## Artifact for the paper "Contract-based Resource Verification for Higher-order Functions with Memoization"

Virtual disk image containing the artifact: [popl-paper-184-artifact.tar.gz](http://lara.epfl.ch/~kandhada/popl-artifact/popl-paper-184-artifact.tar.gz)

The above vdi image is pre-installed with the following artifacts:

1. The sources and executables of the resource verification system (Leon/Orb) described in the paper.
2. Sources of all benchmarks used in the evaluation.
3. All results and data used in the evaluation and presented in Figures 9 and 10 of the paper. 

Below we provide instructions for running our resource verification system (Leon/Orb) on the benchmarks, and 
for reproducing the results of the paper. Our tool can also be tried online on some benchmarks
at [leondev.epfl.ch](http://leondev.epfl.ch) (Memresource section). 
To know more about our tool and for getting started on writing and verifying new programs with Leon/Orb
please refer to the documentation http://leondev.epfl.ch/doc/resourcebounds.html.

## Booting the virtual disk image

1. Install [Oracle Virtual Box](https://www.virtualbox.org/wiki/Downloads). 
2. Extract the .vdi file from the archive
3. Create a new virtual machine with the downloaded .vdi file as the hard disk. Our benchmarks are compute intensive. **We recommend at least 4GB of RAM and 2 Processing Cores for the virtual machine.** (Some benchmarks could timeout on lower configurations.)
4. When started, the virtual machine should boot Xubuntu 16.04 Linux operating system and will automatically log into the account : *popl* (password: *popl*)
    
## Running the tool on all benchmarks - Reproducing results of Figure 9

As shown in Figure 9 of the paper, a total of 17 benchmarks are used in the evaluation. Each benchmark has two versions one with a `steps` bound, which denotes the number evaluation steps, and another with a `alloc` resource bound, which denotes the number of heap-allocated objects. The version with `steps` bound can be found in `~/leon/testcases/benchmark/steps` and
the ones with `alloc` bounds can be found in `~/leon/testcases/benchmark/alloc`. 
The results of running the tool on these benchmarks are available in the folders inside the `~/leon/results/` directory. The folder `~/leon/results/server-results` has the results of running the benchmarks on a machine with the configurations presented in the paper, and provides more accurate data for the time taken by tool on a benchmark.

To infer the `steps` bounds of the benchmarks (shown in Figure 9), use the following commands:

    $ cd ~/leon/results
    $ mkdir steps; cd steps
    $ ../../scripts/steps.sh

To infer the `alloc` bounds of the benchmarks, replace `steps` by `alloc` in the above commands. The script will take about half-an-hour (depending on the VM configuration) to verify all benchmarks. 

#### Understanding the output of the tool 

Running the script produces two files: `<benchmarkname>-stats.txt` and `<benchmarkname>.out`  file for each benchmark. The `-stats` file provides several statistics in the form of "key : value" pairs, and has all the  bounds inferred for every function (that has a template) in the benchmark. Note that Figure 9 of the paper shows only the bounds inferred for a couple of functions in each benchmark (for each resource). Below we list the functions in each benchmark whose bounds were presented in Figure 9. Reviewers may restrict their attention to these functions in all of the evaluations/results that follow.

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

#### Descrption of the Stats file

At the end of each stats file there are two tables: **Resource Verification** and **State Verification**.
The former table shows the inferred bounds for every function (including those presented in Figure 9), and the latter table  shows the result of verifying the correctness invariants needed for proving the resource bounds, which may possibly depend on the state of the memoization. All invariants in all the benchmarks will be verified by the tool and would be marked as **valid**. The table also shows the SMT solver (one of CVC4 or Z3) that first succeeded in verifying the generated verification conditions. 

Most of the key-value pairs in the stats file present details on the internals of the algorithm. The most relevant entries among these are _Total-Time_ (The column AT of Figure 9), _State-Verification-Time_ and _Resource-Verification-Time_.

#### Minor Variances from Figure 9 Results

Even though the tool tries its best effort to enforce determinism, minor variances across different runs (although rare) is possible, especially for highly nonlinear bounds. This is because of the incompleteness of the minimization problem in the presence of nonlinearity and recursive functions, and the non-determinism in SMT solvers. Therefore, the constants inferred by the tool may slightly vary compared to Figure 9 rarely. We observed a deviance greater than +/- 1 on an inferred constant on the two benchmarks: _PackratParsing_ and _Deque_ (for  the `steps` resource). In both cases the tool computed a more precise bound than the one presented in Figure 9.

## Measuring the accuracy of the inferred bounds - Reproducing the results of Figure 10

To carry out the experiment whose results are shown in Figure 10, we instrument the benchmark to track the resources (using `./leon --instrument` option), and add drivers to run the benchmarks with inputs that execise the worst-case behavior. 
All such instrumented benchmarks (having an executable `main` function) can found in the folder: `~/leon/RuntimeEvaluation/src/main/scala/steps` (or alloc).  
The `main` function of each benchmark runs the benchmark on many inputs, computes the dynamic resource usage, and compares it against the statically inferred bounds as described in the section 5 of the paper. Use the following commands to execute the instrumented benchmarks.

    $ cd ~/leon/RuntimeEvaluation/
    $ sbt                            ## invokes the scala build tool
    
Once inside the `sbt` prompt, use the following comands

    > run
    
The `run` command will list all the avaiable benchmarks that can be executed. Choose the benchmark to run by entering its index. Running each benchmark will produce a set of `.data` and `.report` files in the directory: `~/leon/RuntimeEvaluation/results/steps/<Benchmarkname>/` (`steps` can be replaced by `alloc`). 
The content of these files are described shortly.

To compute the summary statistics shown in Figure 10, run the `StatsCollector` program (listed as 1), which outputs the averages shown in Figure 10 to a file `~/RuntimeEvaluation/Figure-10-data`. 

## Outputs of the Instrumented Benchmark

Running each of the instrumented benchmark produces the following files:
*  `dynamic<benchmark-abbrv>.data`
* `paretoanalysis<benchmark-abbrv>.report`
*  One or more `pareto<index><benchmark-abbrv>.data`

Each `.data` file contains a list of triples: (a) the size of the input, (b) the static inferred bound for the input, (c) dynamic resource usage or the pareto optimal resource usage. E.g. the file `dynamicmsort.data` has the following entries

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

Here, for an input of size 1000, the statically inferred steps count was 57318 and the runtime steps count was 54546. 
Using these data for each benchmark, the program `StatsCollector` computes a summary statistics using the formula shown in page 10 of the paper. This quantity is refered to as _dynamic/static * 100_ and is outputted by `StatsCollector` for each benchmark (and each resource) to the file `~/RuntimeEvaluation/Figure-10-data`.

### Comparisons with pareto optimal bounds

As explained in section 5 of the paper, we also compare the statically inferred bounds to a set of  pareto optimal bounds with respect to the dynamic execution. Each of the pareto optimal bound is obtained by reducing a coefficient in the inferred bound, while preserving the other coefficients, until the bound is violated by a concrete input. 
The file `paretoanalysis<benchmark-abbrv>.report` has this data for each benchmark. E.g. the file `paretoanalysishams.report` generated by the benchmark `CyclicHammingStream` _(hams)_ has the following content:
    
    Statically inferred formula: 129*n + 4

    Reducing coeff 0 starting from 4
    Lowest possible value for the coefficient is 4
    Pareto optimal template: 129*n + 4
    First counter-example for 129*n + 3 is at the point 0

    Reducing coeff 1 starting from 129
    Lowest possible value for the coefficient is 124
    Pareto optimal template: 124*n + 4
    First counter-example for 123*n + 4 is at the point 8000

As explained in the report the first coeffcient is optimal and second coefficient could at best be reduced to 124 (without increasing the other coeffecients) for the given dynamic runs. It shows that the data point 8000 violates the bound if the coefficient is reduced to 123.

The files `pareto0hams.data` and `pareto1hams.data` shows the statically inferred bound, and the first and the second pareto optimal bound respectively, for each input. 

Using these data for each benchmark, the program `StatsCollector` computes the metric _optimal/static * 100_ (for each benchmark and resource) and outputs to the file `~/RuntimeEvaluation/Figure-10-data`.

