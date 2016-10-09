package PackratParsing

import leon.collection._
import leon._
import leon.mem._
import leon.lang._
import leon.annotation._
import leon.instrumentation._
import leon.invariant._
import leon.runtimeDriver._


object PackratParsing {
/////////////////////////////////////////////////////////////////////
  abstract class Terminal0
  
  case class Open0() extends Terminal0
  
  case class Close0() extends Terminal0
  
  case class Plus0() extends Terminal0
  
  case class Times0() extends Terminal0
  
  case class Digit0() extends Terminal0
  
  abstract class Result0
  
  case class Parsed0(rest0 : BigInt) extends Result0
  
  case class NoParse0() extends Result0
  
  var istring = Array[Terminal0]()
  def lookuptime0(i51 : BigInt): (Terminal0, BigInt) = ((istring(i51.toInt), 1) : (Terminal0, BigInt))
  
  @invisibleBody
  @invstate
  def pAddmemtime0(i52 : BigInt, st11 : Set[MemoFuns0]): ((Result0, Set[MemoFuns0]), BigInt) = {
    val e32 = pMulmemtime0(i52, st11)
    val e381 = e32._1
    val ir80 = e381._1
    val e391 = e381._2 ++ Set[MemoFuns0](PMulmemM0(i52))
    val r167 = ir80 match {
      case Parsed0(j0) =>
        val c28 = BigInt(5) 
        val mc3 = if (j0 > BigInt(0) && lookuptime0(j0)._1 == Plus0()) {
          val ir74 = j0 - BigInt(1)
          val e47 = pAddmemtime0(ir74, e391)
          val e404 = e47._1
          val e414 = e404._2 ++ Set[MemoFuns0](PAddmemM0(ir74))
          val r164 = e404._1 match {
            case Parsed0(rem0) =>
              ((Parsed0(rem0), e414), BigInt(4))
            case _ =>
              ((ir80, e414), BigInt(2))
          }
          (r164._1, ((BigInt(2) + c28) + r164._2) + (if (e391.contains(PAddmemM0(ir74))) {
            BigInt(1)
          } else {
            BigInt(3) + e47._2
          }))
        } else {
          ((ir80, e391), BigInt(1) + c28)
        }

      (mc3._1, BigInt(3) + mc3._2)
      case _ =>
        ((ir80, e391), BigInt(2))
    }
    (r167._1, r167._2 + (if (st11.contains(PMulmemM0(i52))) {
      BigInt(1)
    } else {
      BigInt(3) + e32._2
    }))
  }
  
  @invisibleBody
  @invstate
  def pMulmemtime0(i55 : BigInt, st12 : Set[MemoFuns0]): ((Result0, Set[MemoFuns0]), BigInt) = {
    val e94 = pPrimmemtime0(i55, st12)
    val e306 = e94._1
    val ir54 = e306._1
    val e316 = e306._2 ++ Set[MemoFuns0](PPrimMem0(i55))
    val r173 = ir54 match {
      case Parsed0(j1) =>
        val c26 = BigInt(5)
        val mc7 = if (j1 > BigInt(0) && lookuptime0(j1)._1 == Times0()) {
          val ir48 = j1 - BigInt(1)
          val e109 = pMulmemtime0(ir48, e316)
          val e329 = e109._1
          val e339 = e329._2 ++ Set[MemoFuns0](PMulmemM0(ir48))
          val r170 = e329._1 match {
            case Parsed0(rem1) =>
              ((Parsed0(rem1), e339), BigInt(4))
            case _ =>
              ((ir54, e339), BigInt(2))
          }
          (r170._1, ((BigInt(2) + c26) + r170._2) + (if (e316.contains(PMulmemM0(ir48))) {
            BigInt(1)
          } else {
            BigInt(3) + e109._2
          }))
        } else {
          ((ir54, e316), BigInt(1) + c26)
        }
        (mc7._1, BigInt(3) + mc7._2)
      case _ =>
        ((ir54, e316), BigInt(2))
    }
    (r173._1, r173._2 + (if (st12.contains(PPrimMem0(i55))) {
      BigInt(1)
    } else {
      BigInt(3) + e94._2
    }))
  }
  
  @invisibleBody
  @invstate
  def pPrimmemtime0(i58 : BigInt, st13 : Set[MemoFuns0]): ((Result0, Set[MemoFuns0]), BigInt) = {
    val e159 = lookuptime0(i58)
    val e225 = e159._1
    val r179 = if (e225 == Digit0()) {
      val e166 = if (i58 > BigInt(0)) {
        (Parsed0(i58 - BigInt(1)), BigInt(4))
      } else {
        (Parsed0(BigInt(-1)), BigInt(3))
      }
      ((e166._1, st13), BigInt(3) + e166._2)
    } else {
      val c20 = BigInt(4)
      val el6 = if (e225 == Open0() && i58 > BigInt(0)) {
        val ir22 = i58 - BigInt(1)
        val e172 = pAddmemtime0(ir22, st13)
        val e237 = e172._1
        val e247 = e237._2 ++ Set[MemoFuns0](PAddmemM0(ir22))
        val r176 = e237._1 match {
          case Parsed0(rem2) =>
            val e189 = lookuptime0(rem2)
            val c22 = BigInt(4) + e189._2
            val e193 = if (rem2 >= BigInt(0) && e189._1 == Close0()) {
              (Parsed0(rem2 - BigInt(1)), BigInt(3) + c22)
            } else {
              (NoParse0(), BigInt(2) + c22)
            }
            ((e193._1, e247), BigInt(3) + e193._2)
          case _ =>
            ((NoParse0(), e247), BigInt(3))
        }
        (r176._1, ((BigInt(2) + c20) + r176._2) + (if (st13.contains(PAddmemM0(ir22))) {
          BigInt(1)
        } else {
          BigInt(3) + e172._2
        }))
      } else {
        ((NoParse0(), st13), BigInt(2) + c20)
      }
      (el6._1, BigInt(3) + el6._2)
    }
    (r179._1, r179._2 + e159._2)
  }
  
  def invokePrimtime0(i65 : BigInt, st18 : Set[MemoFuns0]): ((Result0, Set[MemoFuns0]), BigInt) = {
    val e83 = pPrimmemtime0(i65, st18)
    val e436 = e83._1
    ((e436._1, e436._2 ++ Set[MemoFuns0](PPrimMem0(i65))), if (st18.contains(PPrimMem0(i65))) {
      BigInt(1)
    } else {
      BigInt(3) + e83._2
    })
  }
  
  def invokeMultime0(i68 : BigInt, st19 : Set[MemoFuns0]): ((Result0, Set[MemoFuns0]), BigInt) = {
    val e16 = invokePrimtime0(i68, st19)
    val e286 = e16._1
    val ir41 = e286._2
    val r163 = {
      val _ = e286._1
      val e21 = pMulmemtime0(i68, ir41)
      val e290 = e21._1
      ((e290._1, e290._2 ++ Set[MemoFuns0](PMulmemM0(i68))), BigInt(1) + (if (ir41.contains(PMulmemM0(i68))) {
        BigInt(1)
      } else {
        BigInt(3) + e21._2
      }))
    }
    (r163._1, (BigInt(1) + r163._2) + e16._2)
  }
  
  @invisibleBody
  def invoketime0(i71 : BigInt, st20 : Set[MemoFuns0]): ((Result0, Set[MemoFuns0]), BigInt) = {
    val e211 = invokeMultime0(i71, st20)
    val e361 = e211._1
    val ir67 = e361._2
    val r181 = {
      val _ = e361._1
      val e216 = pAddmemtime0(i71, ir67)
      val e365 = e216._1
      ((e365._1, e365._2 ++ Set[MemoFuns0](PAddmemM0(i71))), BigInt(1) + (if (ir67.contains(PAddmemM0(i71))) {
        BigInt(1)
      } else {
        BigInt(3) + e216._2
      }))
    }
    (r181._1, (BigInt(1) + r181._2) + e211._2)
  }
  
  @invisibleBody
  def parsetime0(n5 : BigInt, st21 : Set[MemoFuns0]): ((Result0, Set[MemoFuns0]), BigInt) = {
    val bd4 = if (n5 == BigInt(0)) {
      val e145 = invoketime0(n5, st21)
      (e145._1, BigInt(3) + e145._2)
    } else {
      val e150 = parsetime0(n5 - BigInt(1), st21)
      val e274 = e150._1
      val r175 = {
        val _ = e274._1
        val e155 = invoketime0(n5, e274._2)
        (e155._1, BigInt(2) + e155._2)
      }
      (r175._1, (BigInt(4) + r175._2) + e150._2)
    }
    (bd4._1, bd4._2)
  }
  
  abstract class MemoFuns0
  
  case class PAddmemM0(i48 : BigInt) extends MemoFuns0
  
  case class PMulmemM0(i49 : BigInt) extends MemoFuns0
  
  case class PPrimMem0(i50 : BigInt) extends MemoFuns0

//////////////////////////////////////////////////////////////////////

 abstract class Terminal
  
  case class Open() extends Terminal
  
  var invokeops = List[BigInt]()
  var paddops = List[BigInt]()
  var pmulops = List[BigInt]()
  var pprimops = List[BigInt]()

  case class Close() extends Terminal
  
  case class Plus() extends Terminal
  
  case class Times() extends Terminal
  
  case class Digit() extends Terminal
  
  abstract class Result
  
  case class Parsed(rest : BigInt) extends Result
  
  case class NoParse() extends Result
  
  var rstring = Array[Terminal]()
  def lookuptime(i : BigInt): (Terminal, BigInt) = ((rstring(i.toInt), 1) : (Terminal, BigInt))
  
  @invisibleBody
  @memoize
  @invstate
  def pAddtime(i : BigInt): (Result, BigInt) = {
    val lr3 = lookup[Result](List(4910, i))
    val ir1 = if (lr3._1) {
      (lr3._2, BigInt(1))
    } else {
      val e52 = pMultime(i)
      pmulops :+= {e52._2}
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
            paddops :+= {e56._2}
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
      pprimops :+= {e71._2}
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
            pmulops :+= {e75._2}
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
          paddops :+= {e25._2}
          (update[Result](List(4909, e147), e25._1), BigInt(4) + e25._2)
        }
        val th3 = scr._1 match {
          case Parsed(rem) =>
            val e33 = lookuptime(rem)
            val c28 = BigInt(4) + e33._2
            val mc = if (rem >= BigInt(0) && e33._1 == Close()) {
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
      pprimops :+= {e46._2}
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
        pmulops :+= {e69._2}
        (update[Result](List(4910, i), e69._1), BigInt(3) + e69._2)
      }
      (mc7._1, (BigInt(2) + mc7._2) + e67._2)
    }
    (bd4._1, bd4._2)
  }
  
  @invisibleBody
  def invoketime(i : BigInt): (Result, BigInt) = {
    val e48 = invokeMultime(i)
    val bd2 = {
      val _ = e48._1
      val lr2 = lookup[Result](List(4909, i))
      val mc2 = if (lr2._1) {
        (lr2._2, BigInt(1))
      } else {
        val e50 = pAddtime(i)
        paddops :+= {e50._2}
        (update[Result](List(4909, i), e50._1), BigInt(3) + e50._2)
      }
      (mc2._1, (BigInt(2) + mc2._2) + e48._2)
    }
    (bd2._1, bd2._2)
  }
  
  @invisibleBody
  def parsetime(n : BigInt): (Result, BigInt) = {
    val bd6 = if (n == BigInt(0)) {
      val e86 = invoketime(n)
      invokeops :+= {e86._2}
      (e86._1, BigInt(3) + e86._2)
    } else {
      val e90 = parsetime(n - BigInt(1))
      val el6 = {
        val _ = e90._1
        val e92 = invoketime(n)
        invokeops :+= {e92._2}
        (e92._1, (BigInt(4) + e92._2) + e90._2)
      }
      (el6._1, BigInt(2) + el6._2)
    }
    (bd6._1, bd6._2)
  }


  def genString(i: Int): Array[Terminal] = {
    // var res = new Array[Terminal](4*i + 1) // Array.fill(4*i + 1){Digit()}
    // var j = 0
    // while(j != i) {
    //   res(3*j) = Open() 
    //   res(3*j + 1) = Digit()
    //   if(j%2 == 0) {
    //     res(3*j + 2) = Plus()
    //   } else {
    //     res(3*j + 2) = Times()
    //   }
    //   j = j + 1
    // }
    // res(3*i) = Digit()
    // j = 0
    // while(j != i) {
    //   res(3*i + j + 1) = Close()
    //   j = j + 1
    // }
    // return res
  
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

    val points = (10 to 200 by 10)// ++ (100 to 2000 by 100) //++ (1000 to 10000 by 1000)
    val size = points.map(x => BigInt(x)).toList
    
    var ops = List[() => BigInt]()
    var orb = List[() => BigInt]()
    // var inst = List[() => BigInt]()
    points.foreach { i =>
      val input = i
      // ops :+= {() => {
          leon.mem.clearMemo()
          rstring =  Array.fill[Terminal](i + 1)(Digit())// genString(i)
          parsetime(i)._2
         // }
       // }
      // inst :+= {() => {
      //   leon.mem.clearMemo()
      //   istring = Array.fill[Terminal0](i + 1)(Digit0())
      //   parsetime0(i, Set[MemoFuns0]())._2
      //   }
      // }
      orb :+= {() => 74 * i + 71}
    }
    // plot(size, ops, inst, "packrat", "inst")
    // plot(size, ops, orb, "packrat", "orb")
    constplot(invokeops, 68, "invoke")
    constplot(paddops, 16, "pAdd")
    constplot(pmulops, 17, "pMul")
    constplot(pprimops, 22, "pPrim")

  }  
  
}
