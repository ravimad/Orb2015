import scala.collection._
import scala.collection.mutable.ListBuffer
import scala.language.implicitConversions
import scala.sys.process._
import scala.math._
import java.io._
import scala.io._

object StatsCollector {
  val resultsDir = "./results/"
  val stepsdir = resultsDir + "steps/"
  val allocdir = resultsDir + "alloc/"
  val benchNames = List( "LazySelectionSort", "PrimeStream",
    "CyclicFibonacciStream", "CyclicHammingStream", "StreamLibrary",
     "RealTimeQueue", "BottomUpMergeSort", "Deque", "LazyNumericalRep", "Conqueue",
        "LCS", "Levenshtein", "HammingMemoized", "WeightedScheduling",
        "Knapsack", "PackratParsing", "Viterbi"
    )
  def main(args: Array[String]): Unit = {
    benchNames.foreach { bn =>
      println("Stats for benchmark: " + bn)
      println("Steps: ")
      resourceStats(stepsdir + bn)
      println("Alloc: ")
      resourceStats(allocdir + bn)
    }
  }

  def resourceStats(benchdirName: String) = {
    // read all the files in the result/ directory
    val benchdir = new File(benchdirName)
    // (a) compute static Vs dynamic
    val dynamic = benchdir.listFiles().filter(fl => fl.getName().startsWith("dynamic"))
    //println("All dynamic files: "+dynamic.mkString(","))
    val dynVstatic = meanRatio(dynamic)
    println("dynamic / static * 100: " + dynVstatic.round)
    // (b) compute pareto optimal stats
    val paretoData = benchdir.listFiles().filter { fl =>
      val name = fl.getName()
      name.startsWith("pareto") && name.endsWith(".data")
    }
    //println("All pareto data files: "+paretoData.mkString(","))
    val paretoVsStatic = meanRatio(paretoData)
    println("optimal / static * 100: " + paretoVsStatic.round)
  }

  def meanRatio(files: Array[File]) = {
    val tmplSum = files.map { fl =>
      // compute the average of each file
      val lines = Source.fromFile(fl).getLines()
      var linecount = 0
      var avgsum = 0.0
      lines.foreach { line =>
        val tokens = line.split(" ").map(_.trim()) // every line has 3 values: entry, orb, ops
        val orb = tokens(1).toDouble
        val ops = tokens(2).toDouble
        if (orb != 0) {
          val avgi = (ops / orb * 100.0)
          linecount += 1
          //println(s"Orb: $orb ops/pareto: $ops avg(i): $avgi")
          avgsum += avgi
        }
      }
      avgsum / linecount
    }.sum
    tmplSum / files.size
  }
}