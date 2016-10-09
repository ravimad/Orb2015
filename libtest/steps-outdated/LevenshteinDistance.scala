package LevenshteinDistance

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
  
  def lookuptime(i : BigInt, j : BigInt): ((BigInt, BigInt), BigInt) = (((xstring(i.toInt), ystring(j.toInt)), BigInt(1)) : ((BigInt, BigInt), BigInt))
  
  @invstate
  @memoize
  @invisibleBody
  def levDisttime(i : BigInt, j : BigInt): (BigInt, BigInt) = {
    val bd = if (i == BigInt(0)) {
      (j, BigInt(2))
    } else {
      val el4 = if (j == BigInt(0)) {
        (i, BigInt(2))
      } else {
        val e16 = lookuptime(i, j)
        val ir = {
          val (xi, yj) = e16._1
          ((xi, yj), BigInt(5) + e16._2)
        }
        val ir14 = ir._1
        val e124 = i - BigInt(1)
        val e126 = j - BigInt(1)
        val lr = lookup[BigInt](List(4881, e124, e126))
        val ir3 = if (lr._1) {
          (lr._2, BigInt(3))
        } else {
          val e27 = levDisttime(e124, e126)
          (update[BigInt](List(4881, e124, e126), e27._1), BigInt(5) + e27._2)
        }
        val ir4 = if (ir14._1 == ir14._2) {
          (ir3._1, BigInt(2))
        } else {
          (BigInt(1) + ir3._1, BigInt(3))
        }
        val e130 = i - BigInt(1)
        val lr1 = lookup[BigInt](List(4881, e130, j))
        val ir5 = if (lr1._1) {
          (lr1._2, BigInt(2))
        } else {
          val e36 = levDisttime(e130, j)
          (update[BigInt](List(4881, e130, j), e36._1), BigInt(4) + e36._2)
        }
        val e134 = j - BigInt(1)
        val lr2 = lookup[BigInt](List(4881, i, e134))
        val ir6 = if (lr2._1) {
          (lr2._2, BigInt(2))
        } else {
          val e41 = levDisttime(i, e134)
          (update[BigInt](List(4881, i, e134), e41._1), BigInt(4) + e41._2)
        }
        val c11 = (ir5._1 >= ir6._1, BigInt(1))
        val r158 = if (ir5._1 >= ir6._1) {
          (ir5._1, BigInt(1) + c11._2)
        } else {
          (ir6._1, BigInt(1) + c11._2)
        }
        val c12 = (ir4._1 >= r158._1, BigInt(1))
        val r160 = if (ir4._1 >= r158._1) {
          (ir4._1, BigInt(1) + c12._2)
        } else {
          (r158._1, BigInt(1) + c12._2)
        }
        (r160._1, ((((((BigInt(4) + r160._2) + r158._2) + ir6._2) + ir5._2) + ir4._2) + ir3._2) + ir._2)
      }
      (el4._1, BigInt(2) + el4._2)
    }
    (bd._1, bd._2)
  }
  
  @invisibleBody
  def invoketime(i : BigInt, j : BigInt, n : BigInt): (BigInt, BigInt) = {
    val lr3 = lookup[BigInt](List(4881, i, j))
    val bd1 = if (lr3._1) {
      (lr3._2, BigInt(1))
    } else {
      val e52 = levDisttime(i, j)
      (update[BigInt](List(4881, i, j), e52._1), BigInt(3) + e52._2)
    }
    (bd1._1, bd1._2)
  }
  
  def bottomuptime(m : BigInt, j : BigInt, n : BigInt): (List[BigInt], BigInt) = {
    val c16 = BigInt(3)
    val bd2 = if (m == BigInt(0) && j == BigInt(0)) {
      val e56 = invoketime(m, j, n)
      (List[BigInt](e56._1), (BigInt(4) + c16) + e56._2)
    } else {
      val el6 = if (j == BigInt(0)) {
        val e64 = bottomuptime(m - BigInt(1), n, n)
        val e68 = invoketime(m, j, n)
        (Cons[BigInt](e68._1, e64._1), (BigInt(6) + e68._2) + e64._2)
      } else {
        val e76 = bottomuptime(m, j - BigInt(1), n)
        val e80 = invoketime(m, j, n)
        (Cons[BigInt](e80._1, e76._1), (BigInt(6) + e80._2) + e76._2)
      }
      (el6._1, (BigInt(1) + c16) + el6._2)
    }
    (bd2._1, bd2._2)
  }
  
  def levDistSolstime(m : BigInt, n : BigInt): (List[BigInt], BigInt) = {
    val e94 = bottomuptime(m, n, n)
    (e94._1, BigInt(1) + e94._2)
  }

  def main(args: Array[String]): Unit = {
    import scala.util.Random
    val rand = Random

    val points = (1 to 30 by 1) ++ (100 to 1000 by 50) // ++ (1000 to 2000 by 50)
    val size = points.map(x => BigInt(x)).to[scalaList]
    val size2 = points.map(x => (x)).toList
    
    var ops = List[BigInt]()
    var orb = List[BigInt]()
    var valuefori2 = scalaList[BigInt]()
    var valuefori = scalaList[BigInt]()
    
    points.foreach { i =>
      val input = i
      xstring = Array.fill(i + 1){0}
      ystring = Array.fill(i + 1){0}
      ops :+= {38*i*i + 39*i + 39*i + 13
          // leon.mem.clearMemo()
          // levDistSolstime(i, i)._2
      }
      orb :+= {39*i*i + 39*i + 39*i + 37}
      valuefori :+= {BigInt(i)}
      valuefori2 :+= {BigInt(i*i)}      
    }
    dumpdata(size2, ops, orb, "levd", "orb")
    // minresults(ops, scalaList(37, 39, 39, 39), List("constant", "i", "i", "i**2"), List(valuefori, valuefori, valuefori2), size, "levensh")
  }  
}
