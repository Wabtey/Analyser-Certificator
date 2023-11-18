package tp67

import utilities.Datatype._
import java.util.ArrayList

object Analyzer {
  def safe(p: statement): Boolean = {
    tp67.san(p, Nil)._2
  }
}
