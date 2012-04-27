package picasso.frontend.dbpGraph

import picasso.utils._

object Main {

  def main(args: Array[String]) {
    Config(args.toList) //process the cmdline args
    Config.input match {
      case fn :: _ => analyse(fn, IO.readTextFile(fn))
      case Nil => analyse("stdin", IO.readStdin)
    }
  }

  
  def analyse(fn: String, content: String) = {
    val analysis =
      if (Config.termination) new Termination(fn, content)
      else new Cover(fn, content)
    analysis.analyse
  }

}
