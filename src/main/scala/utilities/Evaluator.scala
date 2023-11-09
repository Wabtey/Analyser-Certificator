package utilities

import java.util.Scanner
import java.lang.Exception
import scala.math.BigInt.int2bigInt
import utilities.Datatype._

object Natural {

  def apply(numeral: BigInt): Natural = new Natural(numeral max 0)
  def apply(numeral: Int): Natural = Natural(BigInt(numeral))
  def apply(numeral: String): Natural = Natural(BigInt(numeral))

}

class Natural private (private val value: BigInt) {

  override def hashCode(): Int = this.value.hashCode()

  override def equals(that: Any): Boolean = that match {
    case that: Natural => this equals that
    case _ => false
  }

  override def toString(): String = this.value.toString

  def equals(that: Natural): Boolean = this.value == that.value

  def as_BigInt: BigInt = this.value
  def as_Int: Int = if (this.value >= scala.Int.MinValue && this.value <= scala.Int.MaxValue)
    this.value.intValue
  else sys.error("Int value out of range: " + this.value.toString)

  def +(that: Natural): Natural = new Natural(this.value + that.value)
  def -(that: Natural): Natural = Natural(this.value - that.value)
  def *(that: Natural): Natural = new Natural(this.value * that.value)

  def /%(that: Natural): (Natural, Natural) = if (that.value == 0) (new Natural(0), this)
  else {
    val (k, l) = this.value /% that.value
    (new Natural(k), new Natural(l))
  }

  def <=(that: Natural): Boolean = this.value <= that.value

  def <(that: Natural): Boolean = this.value < that.value

}

object HOL {

  trait equal[A] {
    val `HOL.equal`: (A, A) => Boolean
  }
  def equal[A](a: A, b: A)(implicit A: equal[A]): Boolean = A.`HOL.equal`(a, b)

  def eq[A: equal](a: A, b: A): Boolean = equal[A](a, b)

} /* object HOL */

object Lista {

  def map[A, B](f: A => B, x1: List[A]): List[B] = (f, x1) match {
    case (f, Nil) => Nil
    case (f, x :: xs) => f(x) :: map[A, B](f, xs)
  }

  def nulla[A](x0: List[A]): Boolean = x0 match {
    case Nil => true
    case x :: xs => false
  }

  def equal_lista[A: HOL.equal](x0: List[A], x1: List[A]): Boolean = (x0, x1) match {
    case (a :: list, Nil) => false
    case (Nil, a :: list) => false
    case (aa :: lista, a :: list) =>
      HOL.eq[A](aa, a) && equal_lista[A](lista, list)
    case (Nil, Nil) => true
  }

  implicit def equal_list[A: HOL.equal]: HOL.equal[List[A]] = new HOL.equal[List[A]] {
    val `HOL.equal` = (a: List[A], b: List[A]) => equal_lista[A](a, b)
  }
}

object String {

  implicit def equal_char: HOL.equal[Char] = new HOL.equal[Char] {
    val `HOL.equal` = (a: Char, b: Char) => a == b
  }

} /* object String */

object Evaluator {

  import /*implicits*/ String.equal_char, Lista.equal_list

  val sc = new Scanner(System.in)

  abstract sealed class optionE[+A]
  final case object NoneE extends optionE[Nothing]
  final case class SomeE[A](a: A) extends optionE[A]

  def assocV[A: HOL.equal, B](uu: A, x1: List[(A, B)]): optionE[B] = (uu, x1) match {
    case (uu, Nil) => NoneE
    case (x1, (x, y) :: xs) =>
      (if (HOL.eq[A](x, x1)) SomeE[B](y) else assocV[A, B](x1, xs))
  }

  def evalE(x0: expression, e: List[(List[Char], BigInt)]): BigInt = (x0, e) match {
    case (Constant(Int.int_of_integer(s)), e) => s
    case (Variable(s), e) =>
      assocV[List[Char], BigInt](s, e) match {
        case NoneE => BigInt(-1)
        case SomeE(y) => y
      }
    case (Sum(e1, e2), e) => evalE(e1, e) + evalE(e2, e)
    case (Sub(e1, e2), e) => evalE(e1, e) - evalE(e2, e)
  }

  def evalC(x0: condition, t: List[(List[Char], BigInt)]): Boolean = (x0, t) match {
    case (Eq(e1, e2), t) => evalE(e1, t) == evalE(e2, t)
  }

def evalS(xa0: statement, x: List[(List[Char], BigInt)]): List[(List[Char], BigInt)] = (xa0, x) match {
    case (Skip, x) => x
    case (Aff(s, e), t) => (s, evalE(e, t)) :: t
    case (If(c, s1, s2), t) =>
      (if (evalC(c, t)) evalS(s1, t)
      else evalS(s2, t))
    case (Seq(s1,s2), t) => evalS(s2, evalS(s1, t))
    case (Read(s), t) =>
      try {
        print("Read: ")
        val rep = sc.nextLine()
        val x: BigInt = rep.toInt
        ((s, x) :: t)
      } catch {
        case e: NumberFormatException =>
          println("Bad integer, try again!")
          evalS(xa0, x)
      }

    case (Print(e), t) => println("Print: " + evalE(e, t)); t
    case (Exec(e), t) =>
      {
        val res: BigInt = evalE(e, t);
        if (res == BigInt(0)) {
          println("Exec: 0... ATTACK!!")
          throw ExecException //new IllegalArgumentException("Exec 0")
        } else {
          println("Exec: " + res)
          t
        }
      }
  }

  def eval(p: statement): Unit = {
    evalS(p, List())
    ()
  }

  // Evaluator for the automatic testing mode
  def evalS2(xa0: statement, x: List[(List[Char], BigInt)],l:List[Int]): (List[(List[Char], BigInt)],List[Int]) = (xa0, x,l) match {
    case (Skip, x,y) => (x,y)
    case (Aff(s, e), t,y) => ((s, evalE(e, t)) :: t,y)
    case (If(c, s1, s2), t,y) =>
      (if (evalC(c, t)) evalS2(s1, t,y)
      else evalS2(s2, t,y))
    case (Seq(s1,s2), t,y) => {val r= evalS2(s1, t,y); evalS2(s2,r._1,r._2)} 
    case (Read(s), t, x1::y) => ((s,BigInt(x1))::t,y)
    case (Read(s), t, Nil) => (t,Nil)            // if there are not enough values to read we stop the execution!  
    case (Print(e), t,y) => (t,y)
    case (Exec(e), t, y) =>      {
        val res: BigInt = evalE(e, t);
        if (res == BigInt(0)) {
          throw ExecException //("Exec 0")
        } else (t,y)
    }
  }
  

} /* object tp67 */

// The exception warning for the execution of an Exec(0)
case object ExecException extends Exception
