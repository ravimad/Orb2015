package CyclicFibStreamAlloc

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
import scala.collection.immutable.{List => scalaList}

////////////////////////////////

// object ZipWithAndFibStream0 {


//   var gennextwithinst = List[() => BigInt]()
//   var nextwithinst = List[() => BigInt]()
//   var zipwithfunwithinst = List[() => BigInt]() 

//   case class SCons0(x0 : BigInt, tailFun0 : ValOrSusp0)
  
//   abstract class ValOrSusp0
  
//   case class Val0(x1 : SCons0) extends ValOrSusp0
  
//   case class Susp0(fun1 : tSCons0) extends ValOrSusp0
  
//   def zipWithFunalloc0(f126 : BigIntxBigInttBigInt0, xs35 : SCons0, ys4 : SCons0, st11 : Set[MemoFuns0]): ((SCons0, Set[MemoFuns0]), BigInt) = {
//     val e112 = {
//       val (SCons0(x20, _), SCons0(y6, _)) = (xs35, ys4)
//       val e102 = evalBigIntxBigInttBigIntalloc0(f126, x20, y6)
//       val e109 = (ZipWithSuspL0(f126, xs35, ys4), BigInt(0))
//       (SCons0(e102._1, Susp0(e109._1)), (BigInt(2) + e109._2) + e102._2)
//     }
//     ((e112._1, st11), e112._2)
//   }
  
//   def zipWithSuspalloc0(f129 : BigIntxBigInttBigInt0, xs38 : SCons0, ys7 : SCons0, st12 : Set[MemoFuns0]): ((SCons0, Set[MemoFuns0]), BigInt) = {
//     val ir12 = xs38.tailFun0 match {
//       case s16 @ Susp0(f139) =>
//         val e156 = ValOrSusp1.fvalmemalloc0(s16, st12)
//         val e265 = e156._1
//         ((e265._1, e265._2 ++ Set[MemoFuns0](FvalmemM0(s16))), if (st12.contains(FvalmemM0(s16))) {
//           BigInt(0)
//         } else {
//           e156._2
//         })
//       case Val0(x16) =>
//         ((x16, st12), BigInt(0))
//     }
//     val ir36 = ir12._1
//     val ir45 = ir36._2
//     val ir14 = ys7.tailFun0 match {
//       case s16 @ Susp0(f140) =>
//         val e171 = ValOrSusp1.fvalmemalloc0(s16, ir45)
//         val e279 = e171._1
//         ((e279._1, e279._2 ++ Set[MemoFuns0](FvalmemM0(s16))), if (ir45.contains(FvalmemM0(s16))) {
//           BigInt(0)
//         } else {
//           e171._2
//         })
//       case Val0(x16) =>
//         ((x16, ir45), BigInt(0))
//     }
//     val ir40 = ir14._1
//     val e190 = zipWithFunalloc0(f129, ir36._1, ir40._1, ir40._2)
//     zipwithfunwithinst :+= {() => e190._2}
//     (e190._1, (e190._2 + ir14._2) + ir12._2)
//   }
  
//   //val fibstream7 : SCons0 = (SCons0(BigInt(0), Val0(SCons0(BigInt(1), Susp0(() => (genNextalloc0(Set[MemoFuns0]())._1, BigInt(0)))))), BigInt(4))._1
  
//   @invisibleBody
//   def nextalloc0(f132 : SCons0, s77 : SCons0, t377 : SCons0, st13 : Set[MemoFuns0]): ((SCons0, Set[MemoFuns0]), BigInt) = {
//     val bd8 = t377.tailFun0 match {
//       case s16 @ Susp0(f141) =>
//         val e142 = ValOrSusp1.fvalmemalloc0(s16, st13)
//         val e321 = e142._1
//         ((e321._1, e321._2 ++ Set[MemoFuns0](FvalmemM0(s16))), if (st13.contains(FvalmemM0(s16))) {
//           BigInt(0)
//         } else {
//           e142._2
//         })
//       case Val0(x16) =>
//         ((x16, st13), BigInt(0))
//     }
//     (bd8._1, bd8._2)
//   }
  
//   @invisibleBody
//   def nthElemAfterThirdalloc0(n6 : BigInt, f135 : SCons0, s80 : SCons0, t380 : SCons0, st14 : Set[MemoFuns0]): ((BigInt, Set[MemoFuns0]), BigInt) = {
//     val e195 = nextalloc0(f135, s80, t380, st14)
//     nextwithinst :+= {() => e195._2}
//     val e307 = e195._1
//     val ir53 = e307._2
//     val r180 = {
//       val fourth0 @ SCons0(x21, _) = e307._1
//       val mc16 = if (n6 == BigInt(3)) {
//         ((x21, ir53), BigInt(0))
//       } else {
//         val e208 = nthElemAfterThirdalloc0(n6 - BigInt(1), s80, t380, fourth0, ir53)
//         (e208._1, e208._2)
//       }
//       (mc16._1, mc16._2)
//     }
//     (r180._1, r180._2 + e195._2)
//   }

//   val fibstream7 : SCons0 =  {
//     SCons0(BigInt(0), Val0(SCons0(BigInt(1), Susp0(GenNextL0()))))
//   } ensuring {
//     (r158 : SCons0) => true
//   }
  
//   @invisibleBody
//   def genNextalloc0(st15 : Set[MemoFuns0]): ((SCons0, Set[MemoFuns0]), BigInt) = {
//     val e114 = fibstream7
//     val ir9 = e114.tailFun0 match {
//       case s16 @ Susp0(f142) =>
//         val e118 = ValOrSusp1.fvalmemalloc0(s16, st15)
//         val e238 = e118._1
//         ((e238._1, e238._2 ++ Set[MemoFuns0](FvalmemM0(s16))), if (st15.contains(FvalmemM0(s16))) {
//           BigInt(0)
//         } else {
//           e118._2
//         })
//       case Val0(x16) =>
//         ((x16, st15), BigInt(0))
//     }
//     val ir28 = ir9._1
//     val e131 = (AnonFun1L0(), BigInt(0))
//     val e138 = zipWithFunalloc0(e131._1, e114, ir28._1, ir28._2)
//     zipwithfunwithinst :+= {() => e138._2}
//     (e138._1, ((e138._2) + e131._2) + ir9._2)
//   }
  
//   def nthFiballoc0(n9 : BigInt, st16 : Set[MemoFuns0]): ((BigInt, Set[MemoFuns0]), BigInt) = {
//     val e19 = fibstream7
//     val r168 = if (n9 == BigInt(0)) {
//       ((e19.x0, st16), BigInt(0))
//     } else {
//       val ir2 = e19.tailFun0 match {
//         case s16 @ Susp0(f143) =>
//           val e26 = ValOrSusp1.fvalmemalloc0(s16, st16)
//           val e337 = e26._1
//           ((e337._1, e337._2 ++ Set[MemoFuns0](FvalmemM0(s16))), if (st16.contains(FvalmemM0(s16))) {
//             BigInt(0)
//           } else {
//             e26._2
//           })
//         case Val0(x16) =>
//           ((x16, st16), BigInt(0))
//       }
//       val ir62 = ir2._1
//       val ir71 = ir62._2
//       val ir70 = ir62._1
//       val r167 = if (n9 == BigInt(1)) {
//         ((ir70.x0, ir71), BigInt(0))
//       } else {
//         val ir4 = ir70.tailFun0 match {
//           case s16 @ Susp0(f144) =>
//             val e47 = ValOrSusp1.fvalmemalloc0(s16, ir71)
//             val e359 = e47._1
//             ((e359._1, e359._2 ++ Set[MemoFuns0](FvalmemM0(s16))), if (ir71.contains(FvalmemM0(s16))) {
//               BigInt(0)
//             } else {
//               e47._2
//             })
//           case Val0(x16) =>
//             ((x16, ir71), BigInt(0))
//         }
//         val ir66 = ir4._1
//         val ir75 = ir66._2
//         val ir74 = ir66._1
//         val r166 = if (n9 == BigInt(2)) {
//           ((ir74.x0, ir75), BigInt(0))
//         } else {
//           val e72 = nthElemAfterThirdalloc0(n9, e19, ir70, ir74, ir75)
//           (e72._1, e72._2)
//         }
//         (r166._1, r166._2 + ir4._2)
//       }
//       (r167._1, r167._2 + ir2._2)
//     }
//     (r168._1, r168._2)
//   }
  
//   abstract class BigIntxBigInttBigInt0
  
//   case class AnonFun1L0() extends BigIntxBigInttBigInt0
  
//   abstract class tSCons0
  
//   case class ZipWithSuspL0(f123 : BigIntxBigInttBigInt0, xs34 : SCons0, ys3 : SCons0) extends tSCons0
  
//   case class GenNextL0() extends tSCons0
  
//   abstract class MemoFuns0
  
//   case class FvalmemM0(thiss631 : ValOrSusp0) extends MemoFuns0
  
//   @axiom
//   def evalBigIntxBigInttBigIntalloc0(cl2 : BigIntxBigInttBigInt0, a01 : BigInt, a11 : BigInt): (BigInt, BigInt) = {
//     val bd3 = {
//       //val t371 : AnonFun1L0 = cl2
//       val e18 = (a01 + a11, BigInt(0))
//       (e18._1, e18._2)
//     }
//     (bd3._1, bd3._2)
//   }
  
//   @axiom
//   def evaltSConsalloc0(cl3 : tSCons0, st19 : Set[MemoFuns0]): ((SCons0, Set[MemoFuns0]), BigInt) = {
//     val bd5 = cl3 match {
//       case t372 : ZipWithSuspL0 =>
//         val e86 = zipWithSuspalloc0(t372.f123, t372.xs34, t372.ys3, st19)
//         val e222 = e86._1
//         ((e222._1, e222._2), e86._2)
//       case t373 : GenNextL0 =>
//         val e92 = genNextalloc0(st19)
//         gennextwithinst :+= {() => e92._2}
//         val e228 = e92._1
//         ((e228._1, e228._2), e92._2)
//     }
//     (bd5._1, bd5._2)
//   }
// }

// object SCons1 {
  
// }

// object ValOrSusp1 {
//   import ZipWithAndFibStream0._
//   def fvalmemalloc0(thiss632 : ValOrSusp0, st20 : Set[MemoFuns0]): ((SCons0, Set[MemoFuns0]), BigInt) = {
//     val bd11 = thiss632 match {
//       case Susp0(f145) =>
//         val e213 = evaltSConsalloc0(f145, st20)
//         (e213._1, e213._2)
//       case Val0(x19) =>
//         ((x19, st20), BigInt(0))
//     }
//     (bd11._1, bd11._2)
//   }
// }


////////////////////////////////

object ZipWithAndFibStream {
  
  case class SCons2(x320 : BigInt, tailFun1 : ValOrSusp2)
  
  
  abstract class ValOrSusp2
  
  
  case class Val1(x319 : SCons2) extends ValOrSusp2
  
  
  case class Susp1(fun1 : () => (SCons2, BigInt)) extends ValOrSusp2
  
  def zipWithFunalloc(f : (BigInt, BigInt) => (BigInt, BigInt), xs : SCons2, ys : SCons2): (SCons2, BigInt) = {
    val bd7 = {
      val (SCons2(x, _), SCons2(y, _)) = (xs, ys)
      val e65 = f(x, y)
      (SCons2(e65._1, Susp1(() => {
        val e70 = zipWithSuspalloc(f, xs, ys)
        (e70._1, e70._2)
      })), BigInt(2) + e65._2)
    }
    (bd7._1, bd7._2)
  }
  
  def zipWithSuspalloc(f : (BigInt, BigInt) => (BigInt, BigInt), xs : SCons2, ys : SCons2): (SCons2, BigInt) = {
    val e21 = xs.tailFun1 match {
      case s80 @ Susp1(f128) =>
        val lr1 = lookup[SCons2](List(4900, s80))
        val mc2 = if (lr1._1) {
          (lr1._2, BigInt(0))
        } else {
          val e20 = ValOrSusp.fvalalloc(s80)
          (update[SCons2](List(4900, s80), e20._1), e20._2)
        }
        (mc2._1, mc2._2)
      case Val1(x322) =>
        (x322, BigInt(0))
    }
    val e25 = ys.tailFun1 match {
      case s81 @ Susp1(f129) =>
        val lr2 = lookup[SCons2](List(4900, s81))
        val mc4 = if (lr2._1) {
          (lr2._2, BigInt(0))
        } else {
          val e24 = ValOrSusp.fvalalloc(s81)
          (update[SCons2](List(4900, s81), e24._1), e24._2)
        }
        (mc4._1, mc4._2)
      case Val1(x323) =>
        (x323, BigInt(0))
    }
    val e26 = zipWithFunalloc(f, e21._1, e25._1)
    (e26._1, (e26._2 + e25._2) + e21._2)
  }
  
  @invisibleBody
  def nextalloc(f : SCons2, s : SCons2, t : SCons2): (SCons2, BigInt) = {
    val bd = t.tailFun1 match {
      case s79 @ Susp1(f127) =>
        val lr = lookup[SCons2](List(4900, s79))
        val mc = if (lr._1) {
          (lr._2, BigInt(0))
        } else {
          val e16 = ValOrSusp.fvalalloc(s79)
          (update[SCons2](List(4900, s79), e16._1), e16._2)
        }
        (mc._1, mc._2)
      case Val1(x321) =>
        (x321, BigInt(0))
    }
    (bd._1, bd._2)
  }
  
  @invisibleBody
  def nthElemAfterThirdalloc(n : BigInt, f : SCons2, s : SCons2, t : SCons2): (BigInt, BigInt) = {
    val e83 = nextalloc(f, s, t)
    val bd10 = {
      val fourth1 @ SCons2(x, _) = e83._1
      val mc15 = if (n == BigInt(3)) {
        (x, BigInt(0))
      } else {
        val e90 = nthElemAfterThirdalloc(n - BigInt(1), s, t, fourth1)
        (e90._1, e90._2)
      }
      (mc15._1, mc15._2 + e83._2)
    }
    (bd10._1, bd10._2)
  }
  
  val fibstreamalloc : (SCons2, BigInt) = (SCons2(BigInt(0), Val1(SCons2(BigInt(1), Susp1(() => {
    val e75 = genNextalloc
    (e75._1, e75._2)
  })))), BigInt(4))
  
  @invisibleBody
  def genNextalloc(): (SCons2, BigInt) = {
    val e121 = fibstreamalloc._1
    val e37 = e121.tailFun1 match {
      case s82 @ Susp1(f131) =>
        val lr3 = lookup[SCons2](List(4900, s82))
        val mc8 = if (lr3._1) {
          (lr3._2, BigInt(0))
        } else {
          val e36 = ValOrSusp.fvalalloc(s82)
          (update[SCons2](List(4900, s82), e36._1), e36._2)
        }
        (mc8._1, mc8._2)
      case Val1(x325) =>
        (x325, BigInt(0))
    }
    val e38 = zipWithFunalloc((x$3 : BigInt, x$4 : BigInt) => (x$3 + x$4, BigInt(0)), e121, e37._1)
    (e38._1, e38._2 + e37._2)
  }
  
  def nthFiballoc(n : BigInt): (BigInt, BigInt) = {
    val e111 = fibstreamalloc._1
    val r161 = if (n == BigInt(0)) {
      (e111.x320, BigInt(0))
    } else {
      val ir2 = e111.tailFun1 match {
        case s83 @ Susp1(f132) =>
          val lr4 = lookup[SCons2](List(4900, s83))
          val mc10 = if (lr4._1) {
            (lr4._2, BigInt(0))
          } else {
            val e43 = ValOrSusp.fvalalloc(s83)
            (update[SCons2](List(4900, s83), e43._1), e43._2)
          }
          (mc10._1, mc10._2)
        case Val1(x326) =>
          (x326, BigInt(0))
      }
      val r160 = if (n == BigInt(1)) {
        (ir2._1.x320, BigInt(0))
      } else {
        val e45 = (ir2._1, BigInt(0))
        val ir3 = ir2._1.tailFun1 match {
          case s84 @ Susp1(f133) =>
            val lr5 = lookup[SCons2](List(4900, s84))
            val mc12 = if (lr5._1) {
              (lr5._2, BigInt(0))
            } else {
              val e47 = ValOrSusp.fvalalloc(s84)
              (update[SCons2](List(4900, s84), e47._1), e47._2)
            }
            (mc12._1, mc12._2 + e45._2)
          case Val1(x327) =>
            (x327, e45._2)
        }
        val r159 = if (n == BigInt(2)) {
          (ir3._1.x320, BigInt(0))
        } else {
          val e53 = nthElemAfterThirdalloc(n, e111, ir2._1, ir3._1)
          (e53._1, e53._2)
        }
        (r159._1, r159._2 + ir3._2)
      }
      (r160._1, r160._2 + ir2._2)
    }
    (r161._1, r161._2)
  }
  
  def main(args: Array[String]): Unit = {
    import scala.util.Random
    // import ZipWithAndFibStream0._
    val rand = Random

    val points = (0 to 10 by 1)
    val size = points.map(x => BigInt(x)).toList
    
    var ops = List[() => BigInt]()
    var orb = List[() => BigInt]()
    // var inst = List[() => BigInt]()
    points.foreach { i =>
      val input = i
      ops :+= {() => {
          leon.mem.clearMemo()
          nthFiballoc(input)._2
        }
      }
      // inst :+= {() => {
      //     leon.mem.clearMemo()
      //     nthFiballoc0(input, Set[MemoFuns0]())._2
      //   }
      // }
      orb :+= {() => (2*(input))}
      
    }
    for(i <- points) {
      println(s"$i ops=${ops(i)()} orb=${orb(i)()}")
    }

    // dumpdata(scalaList.range(1, gennextwithrun.size.toInt), gennextwithrun, gennextwithinst, "gennext", "inst")
    // dumpdata(scalaList.range(1, nextwithrun.size.toInt), nextwithrun, nextwithinst, "next", "inst")
    // dumpdata(scalaList.range(1, zipwithfunwithrun.size.toInt), zipwithfunwithrun, zipwithfunwithinst, "zipwithfun", "inst")

  }
  
}

object SCons {
  
}

object ValOrSusp {
  def fvalalloc(thiss : ZipWithAndFibStream.ValOrSusp2): (ZipWithAndFibStream.SCons2, BigInt) = {
    val bd2 = thiss match {
      case ZipWithAndFibStream.Susp1(f130) =>
        val e28 = f130()
        (e28._1, e28._2)
      case ZipWithAndFibStream.Val1(x324) =>
        (x324, BigInt(0))
    }
    (bd2._1, bd2._2)
  }
}