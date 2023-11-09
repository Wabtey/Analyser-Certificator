package tp67

import testers._
import utilities.Datatype._
import utilities.Parser
import utilities.ExecException
import utilities.Evaluator
import java.io.File
import scala.io.StdIn._

// The parser for programs in text files
object Main {
  // The main function for the interactive mode
  def main(args: Array[String]): Unit = {
    var rep = ""
    while (rep != "1" && rep != "2") {
      println("Type 1 for running programs or 2 for statistics")
      rep = readLine()
    }
    if (rep == "2") TestDevice.runTests(Analyzer.safe)
    else {
      var fileName = ""
      do {
        fileName = ""
        println("\nGive a program name to evaluate or type q to stop")
        while (fileName == "") {
          print("Program name: ")
          fileName = readLine()
        }
        if (fileName != "q") {
          val f = new File(fileName)
          if (!f.exists()) println("File does not exists, try again!")
          else {
            val p = Parser.parseFile(fileName)
            if (!p.successful) println("Parsing failed! try again!")
            else if (Analyzer.safe(p.get)) {
              println("** Starting evaluation of " + fileName)
              try Evaluator.eval(p.get)
              catch {
                case ExecException => ()
              }
              println("** End of the evaluation of " + fileName)
            } else println(fileName + " was rejected by the analyzer!!")
          }
        }
      } while (fileName != "q")
    }
  }

}
