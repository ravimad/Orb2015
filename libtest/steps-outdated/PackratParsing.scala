package PackratParsing

import leon.collection._
import leon._
import leon.mem._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.invariant._
import leon.runtimeDriver._
import scala.collection.mutable.{ListBuffer => scalaList}
import scala.collection.mutable.{Set => scalaSet}

object PackratParsing {
  abstract class Terminal
  
  case class Open() extends Terminal
  
  case class Close() extends Terminal
  
  case class Plus() extends Terminal
  
  case class Times() extends Terminal
  
  case class Digit() extends Terminal
  
  abstract class Result
  
  case class Parsed(rest : BigInt) extends Result
  
  case class NoParse() extends Result
  
  var pAdd = List[BigInt]()
  var paddinputs = scalaSet[BigInt]()

  var istring = Array[Terminal]()
  def lookuptime(i51 : BigInt): (Terminal, BigInt) = ((istring(i51.toInt), 1) : (Terminal, BigInt))
  
  @invisibleBody
  @memoize
  @invstate
  def pAddtime(i : BigInt): (Result, BigInt) = {
    val lr3 = lookup[Result](List(4910, i))
    val ir1 = if (lr3._1) {
      (lr3._2, BigInt(1))
    } else {
      val e52 = pMultime(i)
      (update[Result](List(4910, i), e52._1), BigInt(3) + e52._2)
    }
    val scr2 = (ir1._1, BigInt(0))
    val r159 = ir1._1 match {
      case Parsed(j) =>
        val c16 = BigInt(5)
        val mc5 = if (j > BigInt(0) && lookuptime(j)._1 == Plus()) {
          val e106 = j - BigInt(1)
          val lr4 = lookup[Result](List(4909, e106))
          val scr3 = if (lr4._1) {
            (lr4._2, BigInt(2))
          } else {
            val e56 = pAddtime(e106)
            if(!paddinputs(e106)) {
              pAdd :+= {e56._2}
              paddinputs += e106
            }
            (update[Result](List(4909, e106), e56._1), BigInt(4) + e56._2)
          }
          val th4 = scr3._1 match {
            case Parsed(rem) =>
              (Parsed(rem), BigInt(4) + scr3._2)
            case _ =>
              (ir1._1, BigInt(2) + scr3._2)
          }
          (th4._1, (BigInt(1) + c16) + th4._2)
        } else {
          (ir1._1, BigInt(1) + c16)
        }
        (mc5._1, (BigInt(3) + mc5._2) + scr2._2)
      case _ =>
        (ir1._1, BigInt(2) + scr2._2)
    }
    (r159._1, r159._2 + ir1._2)
  }
  
  @invisibleBody
  @memoize
  @invstate
  def pMultime(i : BigInt): (Result, BigInt) = {
    val lr6 = lookup[Result](List(4911, i))
    val ir2 = if (lr6._1) {
      (lr6._2, BigInt(1))
    } else {
      val e71 = pPrimtime(i)
      (update[Result](List(4911, i), e71._1), BigInt(3) + e71._2)
    }
    val scr5 = (ir2._1, BigInt(0))
    val r160 = ir2._1 match {
      case Parsed(j) =>
        val c18 = BigInt(5) 
        val mc10 = if (j > BigInt(0) && lookuptime(j)._1 == Times()) {
          val e121 = j - BigInt(1)
          val lr7 = lookup[Result](List(4910, e121))
          val scr6 = if (lr7._1) {
            (lr7._2, BigInt(2))
          } else {
            val e75 = pMultime(e121)
            (update[Result](List(4910, e121), e75._1), BigInt(4) + e75._2)
          }
          val th5 = scr6._1 match {
            case Parsed(rem) =>
              (Parsed(rem), BigInt(4) + scr6._2)
            case _ =>
              (ir2._1, BigInt(2) + scr6._2)
          }
          (th5._1, (BigInt(1) + c18) + th5._2)
        } else {
          (ir2._1, BigInt(1) + c18)
        }
        (mc10._1, (BigInt(3) + mc10._2) + scr5._2)
      case _ =>
        (ir2._1, BigInt(2) + scr5._2)
    }
    (r160._1, r160._2 + ir2._2)
  }
  
  @invisibleBody
  @memoize
  @invstate
  def pPrimtime(i : BigInt): (Result, BigInt) = {
    val e15 = lookuptime(i)
    val e137 = e15._1
    val r158 = if (e137 == Digit()) {
      val th1 = if (i > BigInt(0)) {
        (Parsed(i - BigInt(1)), BigInt(4))
      } else {
        (Parsed(BigInt(-1)), BigInt(3))
      }
      (th1._1, BigInt(3) + th1._2)
    } else {
      val c26 = BigInt(4)
      val el3 = if (e137 == Open() && i > BigInt(0)) {
        val e147 = i - BigInt(1)
        val lr = lookup[Result](List(4909, e147))
        val scr = if (lr._1) {
          (lr._2, BigInt(2))
        } else {
          val e25 = pAddtime(e147)
          if(!paddinputs(e147)) {
            pAdd :+= {e25._2}
            paddinputs += e147
          }
          (update[Result](List(4909, e147), e25._1), BigInt(4) + e25._2)
        }
        val th3 = scr._1 match {
          case Parsed(rem) =>
            val c28 = BigInt(5) 
            val mc = if (rem >= BigInt(0) && lookuptime(rem)._1 == Close()) {
              (Parsed(rem - BigInt(1)), BigInt(3) + c28)
            } else {
              (NoParse(), BigInt(2) + c28)
            }
            (mc._1, (BigInt(3) + mc._2) + scr._2)
          case _ =>
            (NoParse(), BigInt(3) + scr._2)
        }
        (th3._1, (BigInt(1) + c26) + th3._2)
      } else {
        (NoParse(), BigInt(2) + c26)
      }
      (el3._1, BigInt(3) + el3._2)
    }
    (r158._1, r158._2 + e15._2)
  }
  
  def invokePrimtime(i : BigInt): (Result, BigInt) = {
    val lr1 = lookup[Result](List(4911, i))
    val bd1 = if (lr1._1) {
      (lr1._2, BigInt(1))
    } else {
      val e46 = pPrimtime(i)
      (update[Result](List(4911, i), e46._1), BigInt(3) + e46._2)
    }
    (bd1._1, bd1._2)
  }
  
  def invokeMultime(i : BigInt): (Result, BigInt) = {
    val e67 = invokePrimtime(i)
    val bd4 = {
      val _ = e67._1
      val lr5 = lookup[Result](List(4910, i))
      val mc7 = if (lr5._1) {
        (lr5._2, BigInt(1))
      } else {
        val e69 = pMultime(i)
        (update[Result](List(4910, i), e69._1), BigInt(3) + e69._2)
      }
      (mc7._1, (BigInt(2) + mc7._2) + e67._2)
    }
    (bd4._1, bd4._2)
  }
  
  def invoketime(i : BigInt): (Result, BigInt) = {
    val e48 = invokeMultime(i)
    val bd2 = {
      val _ = e48._1
      val lr2 = lookup[Result](List(4909, i))
      val mc2 = if (lr2._1) {
        (lr2._2, BigInt(1))
      } else {
        val e50 = pAddtime(i)
        if(!paddinputs(i)) {
          pAdd :+= {e50._2}
          paddinputs += i
        }
        (update[Result](List(4909, i), e50._1), BigInt(3) + e50._2)
      }
      (mc2._1, (BigInt(2) + mc2._2) + e48._2)
    }
    (bd2._1, bd2._2)
  }
  
  def parsetime(n : BigInt): (Result, BigInt) = {
    val bd6 = if (n == BigInt(0)) {
      val e86 = invoketime(n)
      (e86._1, BigInt(3) + e86._2)
    } else {
      val e90 = parsetime(n - BigInt(1))
      val el6 = {
        val _ = e90._1
        val e92 = invoketime(n)
        (e92._1, (BigInt(4) + e92._2) + e90._2)
      }
      (el6._1, BigInt(2) + el6._2)
    }
    (bd6._1, bd6._2)
  }
  
  def genString(i: Int): Array[Terminal] = {  
    import scala.util.Random
    val rand = Random

    var res = new Array[Terminal](i + 1) // Array.fill(4*i + 1){Digit()}
    var j = 0
    while(j != i + 1) {
      var temp = rand.nextInt(5)
      temp match {
        case 0 => res(j) = Open()
        case 1 => res(j) = Close()
        case 2 => res(j) = Times()
        case 3 => res(j) = Plus()
        case 4 => res(j) = Digit()
      }
      j = j + 1
    }
    return res
  }

  def main(args: Array[String]): Unit = {
    import scala.util.Random
    val rand = Random

    val points = (10 to 200 by 10) ++ (100 to 2000 by 100) ++ (1000 to 10000 by 1000) 
    val size = points.map(x => BigInt(x)).to[scalaList]
    val size2 = points.map(x => (x)).toList
    
    var ops = List[BigInt]()
    var orb = List[BigInt]()
    var valueFori = List[BigInt]()
    points.foreach { i =>
      val input = i
      ops :+= {
          47*i + 70
          // 73*i + 43
          
          // leon.mem.clearMemo()
          // istring = Array.fill[Terminal](i + 1)(Digit())
          // parsetime(i)._2
      }
      orb :+= {73*i + 70}
      valueFori :+= {i}
    }
    // println(pAdd)
    dumpdata(size2, ops, orb, "packrat", "orb")
    // minresults(ops, scalaList(70, 73), List("constant", "i"), List(size), size, "packrat")

  }  
}
