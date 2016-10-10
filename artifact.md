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

## Running the tool on individual source files

The following command can be used to run individual source files. However, to reproduce the results presented in the paper we recommend using the scripts described in the subsequent sections.

    $ /home/popl/leon/leon --mem --benchmark --timeout=<secs> path-to-file

The tool prints log messages and inferred bounds to the console. It dumps the final output and some statistics of the evaluation to a file \<Classname\>-stats.txt in the directory from where the tool was run.
For a short description of the above and other command line options use `leon --help`.
    
## Running the tool on all benchmarks - Reproducing results of Figure 9

As shown in Figure 9 of the paper, a total of 17 benchmarks are used in the evaluation. Each benchmark has two versions one with a `steps` bound, which denotes the number evaluation steps, and another with a `alloc` resource bound, which denotes the number of heap-allocated objects. The versions with `steps` bound can be found in `~/leon/testcases/benchmark/steps` and
the ones with `alloc` bounds can be found in `~/leon/testcases/benchmark/alloc`. 
Each benchmark has in its header a brief description (or pointers) to the algorithm that is implemented.
The results of running the tool on these benchmarks are available in the folders inside the `~/leon/results/` directory, organized by date. The folder `~/leon/results/server-results` has the results of running the benchmarks on a machine with the configurations presented in the paper, and provides more accurate data for the time taken by tool on a benchmark.

To infer the `steps` bounds of the benchmarks (shown in Figure 9), use the following scripts:

    $ cd ~/leon/results
    $ mkdir steps; cd steps
    $ ../../scripts/steps.sh

To infer the `alloc` bounds of the benchmarks, replace `steps` by `alloc` in the above commands. The script will take about half-an-hour (depending on the VM configuration) to verify all benchmarks. 

#### Understanding the output of the tool 

Running the script produces a `<benchmarkname>-stats.txt` and `<benchmarkname>.out`  file for each benchmark. The `-stats` file provides several statistics in the form of "key : value" pairs, and has all the  bounds inferred for every function (that has a template) in the benchmark. Note that Figure 9 of the paper shows only the bounds inferred for a couple of functions in each benchmark (for each resource). Below we list the functions in each benchmark whose bounds were presented in Figure 9. The bounds inferred for these functions are most relevant and constitute the top-level bounds. (Nonetheless, benchmarks like `Conqueue` and `StreamLibrary` have many other top-level functions that are interesting.) Reviewers may restrict their attention to these functions in all of the evaluations/results that follow.

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
The former table shows the inferred bounds for every function (presented in Figure 9), and the latter table  shows the result of verifying the (correctness) invariants needed for proving the resource bounds, which may possibly depend on the state of the memoization. All invariants in all the benchmarks will be verified by the tool and would/should be marked as **valid**. The table also shows the SMT solver (one of CVC4 or Z3) that first succeeded in verifying the generated verification conditions. 

Most of the key-value pairs in the stats file present details on the internals of the algorithm. The most relevant entries among these are _Total-Time_ (The column AT of Figure 9), _State-Verification-Time_ and _Resource-Verification-Time_.

#### Minor Variances from Figure 9 Results

Even though the tool tries its best effort to enforce determinism, minor variances across different runs (although rare) is possible, especially for highly nonlinear bounds. This is because of the incompleteness of the minimization problem in the presence of nonlinearity and recursive functions, and the non-determinism in SMT solvers. Therefore, the constants inferred by the tool may slightly vary compared to Figure 9 rarely. We observed a deviance greater than +/- 1 on an inferred constant on the two benchmarks: _PackratParsing_ and _Deque_ (for  the `steps` resource). In both cases the tool computed a more precise bound than the one presented in Figure 9.

## Measuring the accuracy of the inferred bounds - Reproducing the results of Figure 10

To run the experiments whose results are shown in Figure 10, the benchmarks need to be instrumented to track the resources, and have to be run with inputs that execise the worst-case behavior. Our tool can be used to output instrumented programs using the `--instrument` option.  All such instrumented benchmarks (having an executable `main` function) can found in the folder: `~/leon/RuntimeEvaluation/src/main/scala/steps` (or alloc).  The `main` function of each benchmark runs the benchmark on many inputs, compute the dynamic resource usage, and compares it against the statically inferred bounds as described in the section 5 of the paper. Below we describe the procedure for reproducing the results of Figure 10.

    $ cd ~/leon/RuntimeEvaluation/
    $ sbt                            ## invokes the scala build tool
    
Once inside the `sbt` prompt, use the following comands

    > run
    
The `run` command will list all the avaiable benchmarks that can be executed. Choose the benchmark to run by typing its number in the listing. Runing each benchmark will produce a set of `.data` and `.report` files in the directory: `~/leon/RuntimeEvaluation/results/steps/<Benchmarkname>/` (replace `steps` by `alloc` when appropriate). 
To compute the summary statistics run the `StatsCollector` benchmark (listed as 1), which present the results of Figure 10 to a file `~/RuntimeEvaluation/Figure-10-data`. We first describe the outputs of running each benchmark, and later the contents of the `Figure-10-data` file.

    




