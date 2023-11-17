package tp67

import utilities.Datatype._

object Analyzer {
  def safe(p: statement): Boolean = {
    tp67.sanconstant(p)
  }
}
