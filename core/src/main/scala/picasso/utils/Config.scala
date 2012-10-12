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
  
  private var options = List[Arg.Def]()

  def newOption(opt: Arg.Key, fct: Arg.Spec, doc: Arg.Doc) {
    options = (opt, fct, doc) :: options
  }
  
  var input: List[String] = Nil
  /** process arguments that do not belong to an option (i.e. the input files). */
  def default(arg: String) {
    input = arg :: input
  }
  
  //verbosity
  newOption("-v", Arg.Unit(() => Logger.moreVerbose), "increase the verbosity level.")
  newOption("-q", Arg.Unit(() => Logger.lessVerbose), "decrease the verbosity level.")
  newOption("--hide", Arg.String( str => Logger.disallow(str)), "hide the output with given prefix.")
  newOption("--noAssert", Arg.Unit(() => Logger.disableAssert), "remove some assertions.")

  //general reporting option
  var report = false
  var reportOutput: Option[String] = None
  var stats = false

  newOption("-r", Arg.Unit(() => report = true), "output a report (with a default name).")
  newOption("--report", Arg.String(str => { report = true; reportOutput = Some(str) } ), "output a report with given name.")
  newOption("--stats", Arg.Unit(() => stats = true), "print statistics about the execution.")

  //general config stuff
  var maxChildren = -1
  newOption("--maxChildren", Arg.Int ( i => maxChildren = i), "limit the number of children that can be spawed at the same time (default: no limit).")

  //about the KM tree analysis
  var KM_showTree = false
  var KM_fullTree = false

  newOption("-t", Arg.Unit(() => KM_showTree = true), "output the Karp-Miller tree (when applicable) as part of the report.")
  newOption("--full", Arg.Unit(() => KM_fullTree = true), "keep all the successors in the Karp-Miller tree.")

  //transition on the cover
  var TGCover = false
  var TGFull = false
  var interfaceExtraction = false

  newOption("--TG", Arg.Unit(() => TGCover = true), "print a graph of the transitions applied to the covering set.")
  newOption("--fullTG", Arg.Unit(() => TGFull = true), "keep all the covering edges when making the transition graph.")
  newOption("--interface", Arg.Unit(() => interfaceExtraction = true), "extract an interface. (many assumptions about the input ...)")

  //about the termination analysis
  var termination = false
  var armcCmd = "armc"
  var princessCmd = "princess"
  var solverCmd = Array("z3", "-smt2", "-in")
  var makeTPreds = false
  var cyclesBound = -1
  var dumpArmc = ""
  var eliminateVar = List[String]()
  var namedTPreds = List[Array[String]]()

  newOption("--termination", Arg.Unit(() => termination = true), "Compute the termination of the system.")
  newOption("--armc", Arg.String(str => armcCmd = str), "The command to call ARMC.")
  newOption("--princess", Arg.String(str => princessCmd = str), "The command to call princess.")
  newOption("--smtSolver", Arg.String(str => solverCmd = str.split(" ")), "The smt sovler (+ options) to use (default: \"z3 -smt2 -in\").")
  newOption("--makeTPreds", Arg.Unit(() => makeTPreds = true), "Generate (many) transition predicates for ARMC.")
  newOption("--cyclesBound", Arg.Int(i => cyclesBound = i), "bound for the number of cycles to consider when generating the transition predicates")
  newOption("--dump", Arg.String(str => dumpArmc = str), "save the ARMC file in the given location rather than run ARMC.")
  newOption("--eliminateVar", Arg.String(str => eliminateVar = str::eliminateVar), "Eliminate the varibles whose name starts with the given prefix.")
  newOption("--namedTPreds", Arg.String(str => namedTPreds = str.split(",") :: namedTPreds), "Generate transition predicates for ARMC by summing variables with given names (separated with ',').")

  val usage = "..."

  def apply(args: Seq[String]) {
    Arg.process(options, default, usage)(args)
  }

}

/** default configuration object */
object Config extends Config {
}
