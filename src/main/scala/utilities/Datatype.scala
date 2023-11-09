package utilities

object Datatype{
	// The type of statements and and expressions (exported from the Isabelle/HOL theory)
  
	
	abstract sealed class expression extends Serializable
	final case class Constant(a: Int.int) extends expression
	final case class Variable(a: List[Char]) extends expression
	final case class Sum(a: expression, b: expression) extends expression
	final case class Sub(a: expression, b: expression) extends expression

	abstract sealed class condition extends Serializable
	final case class Eq(a: expression, b: expression) extends condition

	abstract sealed class statement extends Serializable
  final case class Seq(a: statement, b: statement) extends statement
  final case class Aff(a: List[Char], b: expression) extends statement
  final case class Read(a: List[Char]) extends statement
  final case class Print(a: expression) extends statement
  final case class Exec(a: expression) extends statement
  final case class If(a: condition, b: statement, c: statement) extends statement
  final case object Skip extends statement
	
  
	object Code_Numeral {
		def integer_of_int(x0: Int.int): BigInt = x0 match {
			case Int.int_of_integer(k) => k
		}
	} /* object Code_Numeral */

	object Int {
		abstract sealed class int
		final case class int_of_integer(a: BigInt) extends int

		def equal_inta(k: int, l: int): Boolean =
		Code_Numeral.integer_of_int(k) == Code_Numeral.integer_of_int(l)

		implicit def equal_int: HOL.equal[int] = new HOL.equal[int] {
			val `HOL.equal` = (a: int, b: int) => equal_inta(a, b)
		}

		def plus_int(k: int, l: int): int =
				int_of_integer(Code_Numeral.integer_of_int(k) +
						Code_Numeral.integer_of_int(l))

		def zero_int: int = int_of_integer(BigInt(0))

		def minus_int(k: int, l: int): int =
			int_of_integer(Code_Numeral.integer_of_int(k) -
					Code_Numeral.integer_of_int(l))

		def uminus_int(k: int): int =
		int_of_integer((- (Code_Numeral.integer_of_int(k))))

	} /* object Int */
}