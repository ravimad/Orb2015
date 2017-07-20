LEON_HOME="/home/kandhada/leon/Orb2015"
#${LEON_HOME}/leon --inferInv --benchmark --minbounds=0 --vcTimeout=3 --timeout=1800  ${LEON_HOME}/testcases/orb-testcases/timing/PropositionalLogic.scala | tee PropositionalLogic.out # < 10s
#${LEON_HOME}/leon --inferInv --benchmark --minbounds=0 --vcTimeout=3 --timeout=1800  ${LEON_HOME}/testcases/orb-testcases/timing/BinomialHeap.scala | tee BinomialHeap.out # < 10s
#${LEON_HOME}/leon --inferInv --benchmark --minbounds=0 --vcTimeout=3 --timeout=1800  ${LEON_HOME}/testcases/orb-testcases/timing/LeftistHeap.scala  | tee LeftistHeap.out # < 20s
#${LEON_HOME}/leon --inferInv --benchmark --minbounds=0 --vcTimeout=3 --timeout=1800  ${LEON_HOME}/testcases/orb-testcases/timing/AVLTree.scala | tee AVLTree.out # < 30s
#${LEON_HOME}/leon --inferInv --benchmark --minbounds=0 --vcTimeout=3 --timeout=1800  ${LEON_HOME}/testcases/orb-testcases/timing/RedBlackTree.scala  | tee RedBlackTree.out # < 40s
#${LEON_HOME}/leon --inferInv --benchmark --minbounds=0 --vcTimeout=3 --timeout=1800  ${LEON_HOME}/testcases/orb-testcases/timing/AmortizedQueue.scala  | tee AmortizedQueue.out # < 40s
#${LEON_HOME}/leon --inferInv --benchmark --minbounds=0 --vcTimeout=3 --timeout=1800  ${LEON_HOME}/testcases/orb-testcases/timing/ConcatVariations.scala | tee ConcatVariations.out # < 40s
#${LEON_HOME}/leon --inferInv --benchmark --minbounds=0 --vcTimeout=3 --timeout=1800  ${LEON_HOME}/testcases/orb-testcases/timing/ListOperations.scala  | tee ListOperations.out # < 40s
#${LEON_HOME}/leon --inferInv --benchmark --minbounds=0 --vcTimeout=3 --timeout=1800  ${LEON_HOME}/testcases/orb-testcases/timing/SortingCombined.scala | tee SortingCombined.out # < 10s
#${LEON_HOME}/leon --inferInv --benchmark --minbounds=0 --vcTimeout=3 --timeout=1800  ${LEON_HOME}/testcases/orb-testcases/timing/BinaryTrie.scala | tee BinaryTrie.out # < 10s
#${LEON_HOME}/leon --inferInv --benchmark --minbounds=0 --vcTimeout=3 --timeout=1800  ${LEON_HOME}/testcases/orb-testcases/timing/InsertionSort.scala  | tee InsertionSort.out # < 20s
#${LEON_HOME}/leon --inferInv --benchmark --minbounds=0 --vcTimeout=3 --timeout=1800  ${LEON_HOME}/testcases/orb-testcases/timing/SpeedBenchmarks.scala | tee SpeedBenchmarks.out # < 30s
#${LEON_HOME}/leon --inferInv --benchmark --minbounds=0 --vcTimeout=3 --timeout=1800  ${LEON_HOME}/testcases/orb-testcases/timing/TreeOperations.scala  | tee TreeOperations.out # < 40s
#${LEON_HOME}/leon --inferInv --benchmark --minbounds=0 --vcTimeout=3 --timeout=1800  ${LEON_HOME}/testcases/orb-testcases/timing/ForElimination.scala  | tee ForElimination.out # < 40s
#${LEON_HOME}/leon --inferInv --benchmark --minbounds=0 --vcTimeout=3 --timeout=1800  ${LEON_HOME}/testcases/orb-testcases/timing/ConstantPropagation.scala  | tee ConstantPropagation.out # < 40s
${LEON_HOME}/leon --inferInv --benchmark --minbounds=0 --vcTimeout=3 --timeout=1800 --disableInfer  ${LEON_HOME}/testcases/orb-testcases/timing/MergeSort.scala | tee Mergesort.out
${LEON_HOME}/leon --inferInv --benchmark --minbounds=0 --vcTimeout=3 --timeout=1800 --disableInfer --assumepreInf  ${LEON_HOME}/testcases/orb-testcases/timing/QuickSort.scala | tee QuickSort.out
${LEON_HOME}/leon --inferInv --benchmark --minbounds=0 --vcTimeout=3 --timeout=1800 --disableInfer --nlTimeout=3  ${LEON_HOME}/testcases/orb-testcases/timing/HeapSort.scala | tee HeapSort.out