package picasso.frontend

import picasso.utils._
import picasso.model.dbp._

abstract class Runner {

  type P <: DBCT
  def parse: String => Option[(DepthBoundedProcess[P], DepthBoundedConf[P], Option[DepthBoundedConf[P]])]

  def main(args: Array[String]) {
    Config(args.toList) //process the cmdline args
    Config.input match {
      case fn :: _ => analyse(fn, IO.readTextFile(fn))
      case Nil => analyse("stdin", IO.readStdin)
    }
  }

  
  def analyse(fn: String, content: String) = {
    val analysis =
      if (Config.termination) new Termination(fn, content, parse)
      else new Cover(fn, content, parse)
    analysis.analyse
  }

}
