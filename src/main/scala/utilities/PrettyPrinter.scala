package utilities

import Datatype._

// Basic PrettyPrinter for programs
object PrettyPrinter{
  var indent:Int=0
    
  def indentation={
    var res=""
    for (i <- 0 until indent){
      res=res+"  "
    }
    res
  }
  
  def stringOf(l:List[Char]):String={
	l match {
	  case Nil => ""
	  case c::r => c.toString()+stringOf(r)
	}
  }
  
  def stringOf(e:expression):String={
    e match {
      case Constant(i) => i.toString
      case Variable(v) => stringOf(v)
      case Sum(e1,e2) => "("+stringOf(e1)+" + "+stringOf(e2)+")"
      case Sub(e1,e2) => "("+stringOf(e1)+" - "+stringOf(e2)+")"
    }
  }
  
  def stringOf(s:statement):String={
    var res=""
    s match {
      case Print(e) => indentation+"print("+stringOf(e)+")\n"
      case Aff(v,e) => indentation+stringOf(v)+":= "+stringOf(e)+"\n"
      case If(Eq(e1,e2),s1,s2) => indentation+"if ("+stringOf(e1)+"="+stringOf(e2)+") then\n"+{indent=indent+2;""}+stringOf(s1)+{indent=indent-2;indentation}+"else\n"+{indent=indent+2;""}+stringOf(s2)+{indent=indent-2;"\n"}
      case Exec(e) => indentation+"exec("+stringOf(e)+")"+"\n"
      case Read(v) => indentation+"read("+stringOf(v)+")"+"\n"
      case Skip => "Skip\n"
      case Seq(s1,s2) => indentation+"{\n"+{
          indent=indent+1
          res=toString(Seq(s1,s2))
          indent=indent-1
          res} + indentation+"}\n"
    }
  }
  
  def toString(s:Seq):String={
    s match {
    case Seq(Seq(s1,s2),Seq(s3,s4)) => toString(Seq(s1,s2))+toString(Seq(s3,s4))
    case Seq(Seq(s1,s2),i) => toString(Seq(s1,s2))+stringOf(i)
    case Seq(i,Seq(s1,s2)) => stringOf(i)+toString(Seq(s1,s2))
    case Seq(i,j) => stringOf(i)+stringOf(j)
    }
  }
}

