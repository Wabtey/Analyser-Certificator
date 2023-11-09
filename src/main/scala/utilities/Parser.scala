package utilities

import scala.util.parsing.combinator.syntactical.StdTokenParsers
import scala.io.Source
import utilities.Datatype._
import scala.util.parsing.combinator.lexical.StdLexical


object Parser extends StdTokenParsers {
  type Tokens = StdLexical

  import lexical.{ Keyword, NumericLit, StringLit, Identifier }

  val lexical = new StdLexical

  lexical.reserved ++= List("var", "read", "print", "exec", "if", "then", "else", "skip")
  lexical.delimiters ++= List("(", ")", "+", "-", "=", ":=", "{", "}")

  def list2seq(l:List[statement]):statement={
    def aux(l:List[statement]):statement=
      l match {
        case s1::s2::Nil => Seq(s1,s2)
        case s1::r => Seq(s1,aux(r))
        case Nil => Skip
      }
    l match {
      case Nil => Skip
      case s1::Nil => s1
      case _ => aux(l)
    }
  }
  // root file parsing operation
  def parseFile(s:String)=
    statement(new lexical.Scanner(Source.fromFile(s).getLines().mkString("\n")))
    
  // the parser itself
  def block: Parser[statement] = "{" ~ rep1(statement) ~ "}" ^^ { case _ ~ s ~ _ => list2seq(s) }
  def statement: Parser[statement] = skip | read | pprint | varDecl | cond | exec | block

  def skip: Parser[statement] = "skip" ^^ { s => Skip }

  def varDecl: Parser[Aff] = ident ~ ":=" ~ expr ^^ { case s ~ _ ~ e => Aff(s.toList, e) }

  def cond: Parser[If] = "if" ~ "(" ~ condExpr ~ ")" ~ "then" ~ statement ~ "else" ~ statement ^^ { case _ ~ _ ~ e ~ _ ~ _ ~ thenepr ~ _ ~ elseexpr => new If(e, thenepr, elseexpr) }

  def exec: Parser[Exec] = "exec" ~ "(" ~ expr ~ ")" ^^ { case _ ~ _ ~ e ~ _ => Exec(e) }

  def read: Parser[Read] = "read" ~ "(" ~ ident ~ ")" ^^ { case _ ~ _ ~ e ~ _ => Read(e.toList) }

  def pprint: Parser[Print] = "print" ~ "(" ~ expr ~ ")" ^^ { case _ ~ _ ~ e ~ _ => Print(e) }

  def expr: Parser[expression] = sumExp | subExp | unExp
  def factor: Parser[expression] = "(" ~> expr <~ ")"

  def sumExp: Parser[expression] = (unExp ~ "+" ~ expr ^^ { case x ~ _ ~ y => new Sum(x, y) }
    | unExp ~ "+" ~ expr ^^ { case x ~ _ ~ y => new Sum(x, y) })

  def subExp: Parser[expression] = (unExp ~ "-" ~ expr ^^ { case x ~ _ ~ y => new Sub(x, y) }
    | unExp ~ "-" ~ expr ^^ { case x ~ _ ~ y => new Sub(x, y) })

  def unExp: Parser[expression] = integerExp | callVar | factor
  def integerExp: Parser[expression] = numericLit ^^ { case s => Constant(Int.int_of_integer(s.toInt)) }
  def callVar: Parser[expression] = ident ^^ { case s => Variable(s.toList) }
  def operator: Parser[String] = "-" | "+" ^^ { case s => s }

  def condExpr: Parser[condition] = (expr ~ "=" ~ expr) ^^ { case x ~ _ ~ y => new Eq(x, y) }
}
