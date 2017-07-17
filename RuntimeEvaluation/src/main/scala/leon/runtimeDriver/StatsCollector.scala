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
        "Knapsack", "PackratParsing", "Viterbi", "RedBlackTree"
    )
  val pw = new PrintWriter(new File("Figure-10-data"))
  def main(args: Array[String]): Unit = {
    var stepsSum = 0L
    var allocSum = 0L
    var stepsOptSum = 0L
    var allocOptSum = 0L
    benchNames.foreach { bn =>
      println("Stats for benchmark: " + bn)
      pw.println("Stats for benchmark: " + bn)
      println("Steps: ")
      pw.println("Steps: ")
      val (c1, c2) = resourceStats(stepsdir + bn)
      stepsSum += c1
      stepsOptSum += c2
      println("Alloc: ")
      pw.println("Alloc: ")
      val (c3, c4) = resourceStats(allocdir + bn)
      allocSum += c3
      allocOptSum += c4
    }
    pw.println("Steps Avg: ")
    pw.println("dynamic / static * 100: "+(stepsSum / 17.0).round)
    pw.println("optimal / static * 100: "+(stepsOptSum / 17.0).round)
    pw.println("Alloc Avg: ")
    pw.println("dynamic / static * 100: "+(allocSum / 17.0).round)
    pw.println("optimal / static * 100: "+(allocOptSum / 17.0).round)
    pw.close()
  }

  def resourceStats(benchdirName: String) = {
    // read all the files in the result/ directory
    val benchdir = new File(benchdirName)
    // (a) compute static Vs dynamic
    val dynamic = benchdir.listFiles().filter(fl => fl.getName().startsWith("dynamic"))
    //println("All dynamic files: "+dynamic.mkString(","))
    val dynVstatic = meanRatio(dynamic).round
    println("dynamic / static * 100: " + dynVstatic)
    pw.println("dynamic / static * 100: " + dynVstatic)
    // (b) compute pareto optimal stats
    val paretoData = benchdir.listFiles().filter { fl =>
      val name = fl.getName()
      name.startsWith("pareto") && name.endsWith(".data")
    }
    //println("All pareto data files: "+paretoData.mkString(","))
    val paretoVsStatic = meanRatio(paretoData).round
    println("optimal / static * 100: " + paretoVsStatic)
    pw.println("optimal / static * 100: " + paretoVsStatic)
    (dynVstatic, paretoVsStatic)
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