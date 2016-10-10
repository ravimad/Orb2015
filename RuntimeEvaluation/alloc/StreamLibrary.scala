package StreamLibraryalloc

import leon.collection._
import leon._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.mem._
import leon.higherorder._
import leon.collection._
import leon.invariant._
import leon.runtimeDriver._
import scala.collection.mutable.{ListBuffer => scalaList}

object StreamLibrary {
  
  abstract class LList2
  
  
  case class SCons1(x321 : BigInt, tailFun2 : () => (LList2, BigInt)) extends LList2
  
  case class SNil1() extends LList2
  
  def natsFromnalloc(n : BigInt): (LList2, BigInt) = (SCons1(n, () => {
    val e28 = genNextNatFromalloc(n)
    (e28._1, e28._2)
  }), BigInt(2))
  
  def genNextNatFromalloc(n : BigInt): (LList2, BigInt) = {
    val ir5 = BigInt(1) + n
    (SCons1(ir5, () => {
      val e83 = genNextNatFromalloc(ir5)
      (e83._1, e83._2)
    }), BigInt(2))
  }
  
  var natstream = natsFromnalloc(1)._1

  @extern
  def constFun1alloc(n : BigInt): (BigInt, BigInt) = ((0, 0): (BigInt, BigInt))
  
  def mapalloc(f : (BigInt) => (BigInt, BigInt), s : LList2): (LList2, BigInt) = {
    val bd13 = s match {
      case SNil1() =>
        (SNil1(), BigInt(1))
      case l43 @ SCons1(x, _) =>
        val e65 = f(x)
        (SCons1(e65._1, () => {
          val e69 = mapSuspalloc(f, s)
          (e69._1, e69._2)
        }), BigInt(2) + e65._2)
    }
    (bd13._1, bd13._2)
  }
  
  def mapSuspalloc(f : (BigInt) => (BigInt, BigInt), s : LList2): (LList2, BigInt) = {
    val e36 = LList.tailOrNilalloc(s)
    val e38 = mapalloc(f, e36._1)
    (e38._1, e38._2 + e36._2)
  }
  
  def appendListalloc(l : List[BigInt], s : LList2): (LList2, BigInt) = {
    val bd22 = l match {
      case Nil() =>
        (s, BigInt(0))
      case Cons(x, tail) =>
        (SCons1(x, () => {
          val e102 = appendListalloc(tail, s)
          (e102._1, e102._2)
        }), BigInt(2))
    }
    (bd22._1, bd22._2)
  }
  
  def repeatalloc(n : BigInt): (LList2, BigInt) = (SCons1(n, () => {
    val e32 = repeatalloc(n)
    (e32._1, e32._2)
  }), BigInt(2))
  
  def cyclealloc(l : List[BigInt]): (LList2, BigInt) = {
    val bd24 = l match {
      case Nil() =>
        (SNil1(), BigInt(1))
      case Cons(x, t) =>
        (SCons1(x, () => {
          val e107 = cyclealloc(l)
          val e109 = appendListalloc(t, e107._1)
          (e109._1, e109._2 + e107._2)
        }), BigInt(2))
    }
    (bd24._1, bd24._2)
  }
  
  @extern
  def constFun2alloc(n : BigInt): (Boolean, BigInt) = ((true, 0) : (Boolean, BigInt))
  
  def takeWhilealloc(p : (BigInt) => (Boolean, BigInt), s : LList2): (LList2, BigInt) = {
    val bd15 = s match {
      case SNil1() =>
        (SNil1(), BigInt(1))
      case l44 @ SCons1(x, _) =>
        val e78 = p(x)
        val e166 = e78._2
        val mc11 = if (e78._1) {
          (SCons1(x, () => {
            val e74 = takeWhileSuspalloc(p, s)
            (e74._1, e74._2)
          }), BigInt(2) + e166)
        } else {
          (SNil1(), BigInt(1) + e166)
        }
        (mc11._1, mc11._2)
    }
    (bd15._1, bd15._2)
  }
  
  def takeWhileSuspalloc(p : (BigInt) => (Boolean, BigInt), s : LList2): (LList2, BigInt) = {
    val e96 = LList.tailOrNilalloc(s)
    val e98 = takeWhilealloc(p, e96._1)
    (e98._1, e98._2 + e96._2)
  }
  
  @extern
  def constFun3alloc(n : BigInt, m : BigInt): (BigInt, BigInt) = ((0, 0) : (BigInt, BigInt))
  
  def scanalloc(f : (BigInt, BigInt) => (BigInt, BigInt), z : BigInt, s : LList2): (LList2, BigInt) = {
    val bd10 = s match {
      case SNil1() =>
        (SNil1(), BigInt(1))
      case l42 @ SCons1(x, _) =>
        val e50 = f(z, x)
        val e160 = e50._1
        (SCons1(z, () => {
          val e55 = scanSuspalloc(f, e160, s)
          (e55._1, e55._2)
        }), BigInt(2) + e50._2)
    }
    (bd10._1, bd10._2)
  }
  
  def scanSuspalloc(f : (BigInt, BigInt) => (BigInt, BigInt), z : BigInt, s : LList2): (LList2, BigInt) = {
    val e60 = LList.tailOrNilalloc(s)
    val e62 = scanalloc(f, z, e60._1)
    (e62._1, e62._2 + e60._2)
  }
  
  @extern
  def constFun4alloc(n : BigInt): ((BigInt, BigInt), BigInt) = (((0, 0), 0) : ((BigInt, BigInt), BigInt))
  
  def unfoldalloc(f : (BigInt) => ((BigInt, BigInt), BigInt), c : BigInt): (LList2, BigInt) = {
    val e113 = f(c)
    val ir2 = {
      val (x, d) = e113._1
      ((x, d), e113._2)
    }
    val ir9 = ir2._1
    val ir16 = ir9._2
    (SCons1(ir9._1, () => {
      val e121 = unfoldalloc(f, ir16)
      (e121._1, e121._2)
    }), BigInt(2) + ir2._2)
  }
  
  def isPrefixOfalloc(l : List[BigInt], s : LList2): (Boolean, BigInt) = {
    val bd19 = s match {
      case SNil1() =>
        val mc15 = l match {
          case Nil() =>
            (true, BigInt(0))
          case _ =>
            (false, BigInt(0))
        }
        (mc15._1, mc15._2)
      case ss1 @ SCons1(x, _) =>
        val mc18 = l match {
          case Nil() =>
            (true, BigInt(0))
          case ll @ Cons(y, tail) =>
            val mc17 = if (x == y) {
              val e89 = LList.tailOrNilalloc(s)
              val e91 = isPrefixOfalloc(tail, e89._1)
              (e91._1, e91._2 + e89._2)
            } else {
              (false, BigInt(0))
            }
            (mc17._1, mc17._2)
        }
        (mc18._1, mc18._2)
    }
    (bd19._1, bd19._2)
  }
  
  def zipWithalloc(f : (BigInt, BigInt) => (BigInt, BigInt), a : LList2, b : LList2): (LList2, BigInt) = {
    val bd1 = a match {
      case SNil1() =>
        (SNil1(), BigInt(1))
      case al1 @ SCons1(x, _) =>
        val mc3 = b match {
          case SNil1() =>
            (SNil1(), BigInt(1))
          case bl1 @ SCons1(y, _) =>
            val e17 = f(x, y)
            (SCons1(e17._1, () => {
              val e22 = zipWithSuspalloc(f, al1, bl1)
              (e22._1, e22._2)
            }), BigInt(2) + e17._2)
        }
        (mc3._1, mc3._2)
    }
    (bd1._1, bd1._2)
  }
  
  def zipWithSuspalloc(f : (BigInt, BigInt) => (BigInt, BigInt), a : LList2, b : LList2): (LList2, BigInt) = {
    val e41 = LList.tailOrNilalloc(a)
    val e44 = LList.tailOrNilalloc(b)
    val e46 = zipWithalloc(f, e41._1, e44._1)
    (e46._1, (e46._2 + e44._2) + e41._2)
  }

  def main(args: Array[String]): Unit = {
    import scala.util.Random
    val rand = Random

    val points = (10 to 200 by 10) ++ (100 to 2000 by 100) ++ (1000 to 10000 by 1000)
    val size = points.map(x => BigInt(x)).to[scalaList]
    val size2 = points.map(x => (x)).toList

    var ops = List[BigInt]()
    var orb = List[BigInt]()
    points.foreach {  i =>
      val input = {
        (1 to i).foldLeft[List[BigInt]](Nil()) { (f, n) =>
          Cons(i - n + 1, f)  
        }
      }
      ops :+= {
          leon.mem.clearMemo()
          isPrefixOfalloc(input, natstream)._2
      }
      orb :+= {4*i}
    }
    dumpdata(size2, ops, orb, "isPrefixOf", "orb")
    minresults(ops, scalaList(0, 4), List("constant", "l.size"), List(size), size, "isPrefixOf")
  }  
  
}

object LList {
  def tailalloc(thiss : StreamLibrary.LList2): (StreamLibrary.LList2, BigInt) = {
    val bd18 = {
      val StreamLibrary.SCons1(_, tailFun3) = thiss
      val e86 = tailFun3()
      (e86._1, e86._2)
    }
    (bd18._1, bd18._2)
  }
  
  def tailOrNilalloc(thiss : StreamLibrary.LList2): (StreamLibrary.LList2, BigInt) = {
    val bd2 = thiss match {
      case StreamLibrary.SNil1() =>
        (thiss, BigInt(0))
      case _ =>
        val lr = lookup[StreamLibrary.LList2](List(4971, thiss))
        val mc5 = if (lr._1) {
          (lr._2, BigInt(0))
        } else {
          val e25 = tailalloc(thiss)
          (update[StreamLibrary.LList2](List(4971, thiss), e25._1), BigInt(1) + e25._2)
        }
        (mc5._1, mc5._2)
    }
    (bd2._1, bd2._2)
  }
}
