package picasso.utils

object Arg {

  sealed abstract class Spec
  case class Unit(fct: () => scala.Unit) extends Spec
  case class Bool(fct: scala.Boolean => scala.Unit) extends Spec
  case class String(fct: java.lang.String => scala.Unit) extends Spec
  case class Int(fct: scala.Int => scala.Unit) extends Spec
  case class Tuple(lst: List[Spec]) extends Spec

  /** The option keyword, e.g. "-k". It must start with '-'. */
  type Key = java.lang.String

  /** a shot description of what the option does. */
  type Doc = java.lang.String

  type Def = (Key, Spec, Doc)

  private def processOption(spec: Def, args: Seq[java.lang.String]): Seq[java.lang.String] = spec._2 match {
    case Unit(fct) =>
      fct()
      args
    case Bool(fct) =>
      args.headOption match {
        case Some(arg) =>
          Misc.toBoolean(arg) match {
            case Some(b) => fct(b)
            case None => Logger.logAndThrow("Arg", LogWarning, "expected boolean argument for option '"+spec._1+"' found: '" + arg + "'.")
          }
          args.tail
        case None =>
          Logger.logAndThrow("Arg", LogWarning, "no (not enough) argument given for option '"+ spec._1 +"'.")
          args
      }
    case Int(fct) =>
      args.headOption match {
        case Some(arg) =>
          Misc.toInt(arg) match {
            case Some(b) => fct(b)
            case None => Logger.logAndThrow("Arg", LogWarning, "expected integer argument for option '"+spec._1+"' found: '" + arg + "'.")
          }
          args.tail
        case None =>
          Logger.logAndThrow("Arg", LogWarning, "no (not enough) argument given for option '"+ spec._1 +"'.")
          args
      }
    case String(fct) =>
      args.headOption match {
        case Some(arg) =>
          fct(arg)
          args.tail
        case None =>
          Logger.logAndThrow("Arg", LogWarning, "no (not enough) argument given for option '"+ spec._1 +"'.")
          args
      }
    case Tuple(x :: xs) =>
      val rest = processOption((spec._1, x, spec._3), args)
      processOption((spec._1, Tuple(xs), spec._3), rest)
    case Tuple(Nil) =>
      args
  }

  private def specType(s: Spec): java.lang.String = s match {
    case Unit(_)    => ""
    case Bool(_)    => "Bool"
    case String(_)  => "String"
    case Int(_)     => "Integer"
    case Tuple(lst) => lst.map(specType(_)).mkString("", " ", "")
  }

  private def printUsage(specs: Seq[Def], usage: java.lang.String) {
    Console.println("cmd [Option(s)] file(s)")
    Console.println(usage)
    Console.println("Options:")
    for ( (opt, spec, descr) <- specs ) {
      Console.println("  " + opt + " " + specType(spec) + "  " + descr)
    }
  }

  def process(specs: Seq[Def], default: java.lang.String => scala.Unit, usage: java.lang.String)(args: Seq[java.lang.String]) {
    args.headOption match {
      case Some(arg) =>
        if (arg == "-h" || arg == "--help") {
          printUsage(specs, usage)
          sys.exit(0)
        } else if (arg startsWith "-") {
          val args2 = specs.find( s => s._1 == arg) match {
            case Some( spec ) =>
              processOption(spec, args.tail)
            case None =>
              Logger.logAndThrow("Arg", LogWarning, "Ignoring unknown option '" + arg + "'.")
              args.tail
          }
          process(specs, default, usage)(args2)
        } else {
          default(arg)
          process(specs, default, usage)(args.tail)
        }
      case None => ()
    }
  }

}

/** A default configuration class */
class Config {
  
  var input: List[String] = Nil
  /** process arguments that do not belong to an option (i.e. the input files). */
  def default(arg: String) {
    input = arg :: input
  }
  
  //verbosity
  val verbose = ("-v", Arg.Unit(() => Logger.moreVerbose), "increase the verbosity level.")
  val quiet   = ("-q", Arg.Unit(() => Logger.lessVerbose), "decrease the verbosity level.")
  val hide    = ("--hide", Arg.String( str => Logger.disallow(str)), "hide the output with given prefix")

  //general reporting option
  var report = false
  var reportOutput: Option[String] = None

  val reportQuick = ("-r", Arg.Unit(() => report = true), "output a report (with a default name).")
  val reportFull = ("--report", Arg.String(str => { report = true; reportOutput = Some(str) } ), "output a report with given name.")

  //about the KM tree analysis
  var KM_showTree = false
  var KM_fullTree = false

  val tree1 = ("-t", Arg.Unit(() => KM_showTree = true), "output the Karp-Miller tree (when applicable) as part of the report.")
  val tree2 = ("--full", Arg.Unit(() => KM_fullTree = true), "keep all the successors in the Karp-Miller tree.")

  //about the termination analysis
  var termination = false
  var useTree = false
  var armcCmd = "armc"
  val termination1 = ("--termination", Arg.Unit(() => termination = true), "Compute the termination of the system.")
  val termination2 = ("--useTree", Arg.Unit(() => useTree = true), "Termination analysis using the KM tree (default is to use only the cover).")
  val termination3 = ("--armc", Arg.String(str => armcCmd = str), "The command to call ARMC.")

  val usage = "..."

  val options = List(
    verbose, quiet, hide,
    reportQuick, reportFull,
    tree1, tree2,
    termination1, termination2, termination3
  )

  def apply(args: Seq[String]) {
    Arg.process(options, default, usage)(args)
  }

}

/** default configuration object */
object Config extends Config {
}
