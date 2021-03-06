package LongestCommonSubsequence

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

object LongestCommonSubsequence {
  @ignore
  var xstring = Array[BigInt]()
  @ignore
  var ystring = Array[BigInt]()
  
  def lookuptime(i : BigInt, j : BigInt): ((BigInt, BigInt), BigInt) = (((xstring(i.toInt), ystring(j.toInt)), BigInt(1)) : ((BigInt, BigInt), BigInt))

  @invstate
  @memoize
  @invisibleBody
  def lcstime(i : BigInt, j : BigInt): (BigInt, BigInt) = {
    val c14 = BigInt(3)
    val bd = if (i == BigInt(0) || j == BigInt(0)) {
      (BigInt(0), BigInt(1) + c14)
    } else {
      val e16 = lookuptime(i, j)
      val ir = {
        val (xi, yj) = e16._1
        ((xi, yj), BigInt(5) + e16._2)
      }
      val ir7 = ir._1
      val r160 = if (ir7._1 == ir7._2) {
        val e101 = i - BigInt(1)
        val e103 = j - BigInt(1)
        val lr = lookup[BigInt](List(4878, e101, e103))
        val e28 = if (lr._1) {
          (lr._2, BigInt(3))
        } else {
          val e27 = lcstime(e101, e103)
          (update[BigInt](List(4878, e101, e103), e27._1), BigInt(5) + e27._2)
        }
        (BigInt(1) + e28._1, BigInt(3) + e28._2)
      } else {
        val e107 = i - BigInt(1)
        val lr1 = lookup[BigInt](List(4878, e107, j))
        val ir3 = if (lr1._1) {
          (lr1._2, BigInt(2))
        } else {
          val e34 = lcstime(e107, j)
          (update[BigInt](List(4878, e107, j), e34._1), BigInt(4) + e34._2)
        }
        val e111 = j - BigInt(1)
        val lr2 = lookup[BigInt](List(4878, i, e111))
        val ir4 = if (lr2._1) {
          (lr2._2, BigInt(2))
        } else {
          val e39 = lcstime(i, e111)
          (update[BigInt](List(4878, i, e111), e39._1), BigInt(4) + e39._2)
        }
        val c10 = (ir3._1 >= ir4._1, BigInt(1))
        val r158 = if (ir3._1 >= ir4._1) {
          (ir3._1, BigInt(1) + c10._2)
        } else {
          (ir4._1, BigInt(1) + c10._2)
        }
        (r158._1, ((BigInt(2) + r158._2) + ir4._2) + ir3._2)
      }
      (r160._1, ((BigInt(3) + c14) + r160._2) + ir._2)
    }
    (bd._1, bd._2)
  }
  
  @invisibleBody
  def invoketime(i : BigInt, j : BigInt, n : BigInt): (BigInt, BigInt) = {
    val lr3 = lookup[BigInt](List(4878, i, j))
    val bd1 = if (lr3._1) {
      (lr3._2, BigInt(1))
    } else {
      val e52 = lcstime(i, j)
      (update[BigInt](List(4878, i, j), e52._1), BigInt(3) + e52._2)
    }
    (bd1._1, bd1._2)
  }
  
  def bottomuptime(m : BigInt, j : BigInt, n : BigInt): (List[BigInt], BigInt) = {
    val c18 = BigInt(3)
    val bd2 = if (m == BigInt(0) && j == BigInt(0)) {
      val e56 = invoketime(m, j, n)
      (List[BigInt](e56._1), (BigInt(4) + c18) + e56._2)
    } else {
      val el4 = if (j == BigInt(0)) {
        val e64 = bottomuptime(m - BigInt(1), n, n)
        val e68 = invoketime(m, j, n)
        (Cons[BigInt](e68._1, e64._1), (BigInt(6) + e68._2) + e64._2)
      } else {
        val e76 = bottomuptime(m, j - BigInt(1), n)
        val e80 = invoketime(m, j, n)
        (Cons[BigInt](e80._1, e76._1), (BigInt(6) + e80._2) + e76._2)
      }
      (el4._1, (BigInt(1) + c18) + el4._2)
    }
    (bd2._1, bd2._2)
  }
  
  def lcsSolstime(m : BigInt, n : BigInt): (List[BigInt], BigInt) = {
    val e94 = bottomuptime(m, n, n)
    (e94._1, BigInt(1) + e94._2)
  }

  def main(args: Array[String]): Unit = {
    import scala.util.Random
    val rand = Random

    val points = (0 to 30 by 1) ++ (100 to 1000 by 50)  //++ (1000 to 10000 by 50)
    // val size = points.map(x => BigInt(x)).to[scalaList]
    val size2 = points.map(x => (x)).toList
    
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
          lcsSolstime(i, i)._2
      }
      orb :+= {31 + 33*i + 33*i + 33*i*i}
      valuefori :+= {BigInt(i)}
      valuefori2 :+= {BigInt(i*i)}
      
    }
    dumpdata(size2, ops, orb, "lcs", "orb")
    // minresults(ops, scalaList(31, 33, 33, 33), List("constant", "i", "i", "i**2"), List(valuefori, valuefori, valuefori2), size, "lcs")
  }  
  
}
