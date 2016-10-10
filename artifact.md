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

### Booting the Virtual Disk Image

1. Install [Oracle Virtual Box](https://www.virtualbox.org/wiki/Downloads). 
2. Extract the .vdi file from the archive
3. Create a new virtual machine with the downloaded .vdi file as the hard disk. Our benchmarks are compute intensive. **We recommend at least 4GB of RAM and 2 Processing Cores for the virtual machine.** (Some benchmarks could timeout on lower configurations.)
4. When started, the virtual machine should boot Xubuntu 16.04 Linux operating system and will automatically log into the account : *popl* (password: *popl*)

### Running the Tool on Individual Source Files

The following command can be used to run individual source files. However, to reproduce the results we recommend using the scripts decribed in the subsequent sections.

    /home/popl/leon/leon --mem --benchmark --timeout=<secs> path-to-file

The tool prints log messages and inferred bounds to the console. It dumps the final output and some statistics of the evaluation to a file \<Classname\>-stats.txt in the directory from where the tool was run.
For a short description of the above and other command line options use `leon --help`.
    
## Running the Tool on all Benchmarks (Results of Figure 9)

As shown in Figure 9 of the paper, a total of 17 benchmarks are used in the evaluation. Each benchmark has two versions one with a `steps` bound, which denotes the number evaluation steps, and other with a `alloc` resource bound, which denotes the number of heap-allocated objects. The versions with steps bound can be found in `~/leon/testcases/benchmark/steps` and
the versions with alloc bounds can be found in `~/leon/testcases/benchmark/alloc`. 
Each benchmark has in its header a breif description and references to the algorithm that is implemented.
The results of running the tool on these benchmarks are available in the folders inside the `~/leon/results/` directory, organized by date. The folder `~/leon/results/server-results` has the results of running the benchmarks on a machine with the configurations presented in the paper, and provides more accurate information regarding the time taken by verification/inference.

To reproduce the results use the following scripts:

    `cd ~/leon/results` 
    `mkdir steps; cd steps`
    `../../scripts/steps.sh`

For alloc results replace `steps` by `alloc` in the above commands. The script will take about 30min to run all benchmarks.
Below we describe the results of the tool with an illustration.

## Understanding the Output of the Tool 

The script produces a `<benchmarkname>-stats.txt` and `<benchmarkname>.out`  file for each benchmark. The `-stats` file has several statistics in the form of key, value pairs, and has all the  bounds inferred for every function (that has a template) in the benchmark. Note that Figure 9 of the paper shows only the bounds inferred for a couple of functions in each benchmark (for each resource), whereas the `-stats` file has an entry for every function. For the benefit of the reviewers, below we list the functions of the benchmarks whose bounds were presented in Figure 9. The bounds inferred for these functions are most relevant and constitute the top-level bounds. (Nonetheless, benchmarks like `StreamLibrary` and `Conqueue` have many other top-level functions that may be interesting.) Reviewers may restrict their attention to these functions in all of the evaluations/results that follow.

### Key functions for each benchmark

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

### Descrption of the Stats file

At the end of each stats file the inferred bounds for every function are presented as a table titled **Resource Verification**. This table contains the bounds presented in Figure 9. At the top of this table there would be another table titled **State Verification**. This shows the result of verifying the (correctness) invariants needed for proving the resource bounds, which may possibly depend on the state of the memoization. All invariants in all the benchmarks will be verified by the tool and would/should be marked as **valid**. The table also shows the SMT solver (one of CVC4 or Z3) that first succeeded in verifying the generated verification conditions. 

Most of the key-value pairs in the stats file present details on the internals of the algorithm. The most relevant entries among these are _Total-Time_ (The column AT of Figure 9), _State-Verification-Time_ and _Resource-Verification-Time_. The stats files in `~/leon/results/server-results` have more accurate data on analysis time.

### Minor Variances from Figure 9 Results

Most of the constants in the bounds inferred by the tool will be identical to those presented in Figure 9 (for the key functions described above). Even though the tool tries its best effort to enforce determinism, minor variance across different runs of the program (although rare) is possible, especially for highly nonlinear bounds. This is because of the incompleteness of the minimization problem in the presence of nonlinearity and recursive functions, and the non-determinism in SMT solvers. We observed such variance on two benchmarks PackratParsing and Deque for  the `steps` resource. In both cases the tool computed a more precise bound than in Figure 9.

### Reproducing the Results of Figure 15

As described in the paper, for this experiment we automatically generate benchmarks by injecting 3 types of errors. The benchmarks used in this experiment are available in the directory "~/grammar-web/benchmarks". (There are about 300 grammars.) Each benchmark is named as follows "grammarname-[error-type]-[num].gram", where [error-type] is a number between 1 to 3 that indicates the type of the error injected, and [num] is a number between 1 and 10. Each benchmark is compared against their original versions whose names
do not have the [error-type] and [num] fields.

To run the complete experiment execute the script: **regr.sh** from the directory "~/grammar-web". 

The script file consists of a sequence of *sbt* commands, one for each benchmark that is compared.
As before, this will produce a log and a stats file for each comparison. 
Note that this experiment will take several hours to complete. 

To test a few sample benchmarks, open the script file regr.sh and comment out the sbt commands that use the benchmarks that have to be excluded.

For comparison purposes, Fig. 15 also presents the results of the using a different tool CFGAnalyzer on the same set of benchmarks. To generate these results, run the script **cfga-regr.sh** from the directory "~/grammar-web". But, since CFGAnalyzer times out on most of the benchmarks, it may take many hours (much longer than our tool) to complete. As before, it is possible to run only a few experiments by commenting out the lines of the script that use the benchmarks that have to be excluded. The output of each comparison is dumped to a file "[benchmark-name].cfga-out.txt".

### Fields of the Statistics Files

The .stats file that are generated during comparison of grammars have the following fields each of which represents a unique metric (described below). 

* _\#EBNF-rules_ : number of productions in the input grammar. (Note that the input grammar is allowed to be in EBNF form).
