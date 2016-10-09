package LevenshteinDistancealloc

import leon.collection._
import leon._
import leon.mem._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.invariant._
import leon.collection._
import leon.runtimeDriver._
import scala.collection.mutable.{ListBuffer => scalaList}

object LevenshteinDistance {
  @ignore
  var xstring = Array[BigInt]()
  @ignore
  var ystring = Array[BigInt]()
  
  def lookupalloc(i : BigInt, j : BigInt): ((BigInt, BigInt), BigInt) = (((xstring(i.toInt), ystring(j.toInt)), BigInt(0)) : ((BigInt, BigInt), BigInt))
  
  @invstate
  @memoize
  @invisibleBody
  def levDistalloc(i : BigInt, j : BigInt): (BigInt, BigInt) = {
    val bd = if (i == BigInt(0)) {
      (j, BigInt(0))
    } else {
      val el4 = if (j == BigInt(0)) {
        (i, BigInt(0))
      } else {
        val e16 = lookupalloc(i, j)
        val ir = {
          val (xi, yj) = e16._1
          ((xi, yj), e16._2)
        }
        val ir10 = ir._1
        val e97 = i - BigInt(1)
        val e99 = j - BigInt(1)
        val lr = lookup[BigInt](List(4884, e97, e99))
        val ir3 = if (lr._1) {
          (lr._2, BigInt(0))
        } else {
          val e27 = levDistalloc(e97, e99)
          (update[BigInt](List(4884, e97, e99), e27._1), BigInt(1) + e27._2)
        }
        val ir4 = if (ir10._1 == ir10._2) {
          (ir3._1, BigInt(0))
        } else {
          (BigInt(1) + ir3._1, BigInt(0))
        }
        val e103 = i - BigInt(1)
        val lr1 = lookup[BigInt](List(4884, e103, j))
        val ir5 = if (lr1._1) {
          (lr1._2, BigInt(0))
        } else {
          val e36 = levDistalloc(e103, j)
          (update[BigInt](List(4884, e103, j), e36._1), BigInt(1) + e36._2)
        }
        val e107 = j - BigInt(1)
        val lr2 = lookup[BigInt](List(4884, i, e107))
        val ir6 = if (lr2._1) {
          (lr2._2, BigInt(0))
        } else {
          val e41 = levDistalloc(i, e107)
          (update[BigInt](List(4884, i, e107), e41._1), BigInt(1) + e41._2)
        }
        val c11 = (ir5._1 >= ir6._1, BigInt(0))
        val r158 = if (ir5._1 >= ir6._1) {
          (ir5._1, c11._2)
        } else {
          (ir6._1, c11._2)
        }
        val c12 = (ir4._1 >= r158._1, BigInt(0))
        val r160 = if (ir4._1 >= r158._1) {
          (ir4._1, c12._2)
        } else {
          (r158._1, c12._2)
        }
        (r160._1, (((((r160._2 + r158._2) + ir6._2) + ir5._2) + ir4._2) + ir3._2) + ir._2)
      }
      (el4._1, el4._2)
    }
    (bd._1, bd._2)
  }
  
  @invisibleBody
  def invokealloc(i : BigInt, j : BigInt, n : BigInt): (BigInt, BigInt) = {
    val lr3 = lookup[BigInt](List(4884, i, j))
    val bd1 = if (lr3._1) {
      (lr3._2, BigInt(0))
    } else {
      val e52 = levDistalloc(i, j)
      (update[BigInt](List(4884, i, j), e52._1), BigInt(1) + e52._2)
    }
    (bd1._1, bd1._2)
  }
  
  def bottomupalloc(m : BigInt, j : BigInt, n : BigInt): (List[BigInt], BigInt) = {
    val bd2 = if (m == BigInt(0) && j == BigInt(0)) {
      val e56 = invokealloc(m, j, n)
      (List[BigInt](e56._1), BigInt(2) + e56._2)
    } else {
      val el6 = if (j == BigInt(0)) {
        val e64 = bottomupalloc(m - BigInt(1), n, n)
        val e68 = invokealloc(m, j, n)
        (Cons[BigInt](e68._1, e64._1), (BigInt(1) + e68._2) + e64._2)
      } else {
        val e76 = bottomupalloc(m, j - BigInt(1), n)
        val e80 = invokealloc(m, j, n)
        (Cons[BigInt](e80._1, e76._1), (BigInt(1) + e80._2) + e76._2)
      }
      (el6._1, el6._2)
    }
    (bd2._1, bd2._2)
  }
  
  def levDistSolsalloc(m : BigInt, n : BigInt): (List[BigInt], BigInt) = {
    val e94 = bottomupalloc(m, n, n)
    (e94._1, e94._2)
  }

  def main(args: Array[String]): Unit = {
    import scala.util.Random
    val rand = Random

    val points = (1 to 30 by 1) ++ (100 to 1000 by 50) // ++ (1000 to 2000 by 50)
    val size = points.map(x => (x)).toList
    val size2 = points.map(x => BigInt(x)).to[scalaList]

    var ops = List[BigInt]()
    var orb = List[BigInt]()
    var valuefori2 = scalaList[BigInt]()
    var valuefori = scalaList[BigInt]()
    
    points.foreach { i =>
      val input = i
      xstring = Array.fill(i + 1){0}
      ystring = Array.fill(i + 1){0}
      ops :+= {
          leon.mem.clearMemo()
          levDistSolsalloc(i, i)._2
      }
      orb :+= {2*i*i + 2*i + 2*i + 3}
      valuefori :+= {BigInt(i)}
      valuefori2 :+= {BigInt(i*i)}      
    }
    // minresults(ops, scalaList(3, 2, 2, 2), List("constant", "i", "i", "i**2"), List(valuefori, valuefori, valuefori2), size2, "levensh")
    dumpdata(size, ops, orb, "levensh", "orb")
  }  
  
}
