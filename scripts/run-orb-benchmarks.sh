./leon --inferInv --benchmark --minbounds=0 --vcTimeout=3 --timeout=1800  ./testcases/orb-testcases/timing/PropositionalLogic.scala | tee PropositionalLogic.out # < 10s
./leon --inferInv --benchmark --minbounds=0 --vcTimeout=3 --timeout=1800  ./testcases/orb-testcases/timing/BinomialHeap.scala | tee BinomialHeap.out # < 10s
./leon --inferInv --benchmark --minbounds=0 --vcTimeout=3 --timeout=1800  ./testcases/orb-testcases/timing/LeftistHeap.scala  | tee LeftistHeap.out # < 20s
./leon --inferInv --benchmark --minbounds=0 --vcTimeout=3 --timeout=1800  ./testcases/orb-testcases/timing/AVLTree.scala | tee AVLTree.out # < 30s
./leon --inferInv --benchmark --minbounds=0 --vcTimeout=3 --timeout=1800  ./testcases/orb-testcases/timing/RedBlackTree.scala  | tee RedBlackTree.out # < 40s