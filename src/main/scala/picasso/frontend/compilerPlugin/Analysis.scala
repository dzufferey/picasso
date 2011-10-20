package picasso.frontend.compilerPlugin

import scala.tools.nsc._
import scala.tools.nsc.plugins._
import scala.collection.mutable.{HashMap, ListBuffer}
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger, Level, Misc, IO, SysCmd}
import picasso.frontend.compilerPlugin.utils._
import picasso.frontend.compilerPlugin.backend._
import picasso.frontend.compilerPlugin.domains._
import picasso.graph._

class Analysis(val global: Global, val picasso: PicassoPlugin)
    extends AnalysisUniverse 
    with ActorOperations
    with BooleanOperations
    with CollectionOperations 
{
  import global._

  override val runsRightAfter: Option[String] = None
  override val runsAfter: List[String] = List(picasso.name + ".gettersSetters")

  var extractedDBP: Option[DBP] = None
  var initState: Option[DBCC] = None

  val phaseName = picasso.name + ".analyse"

  def newPhase(prev: Phase) = new AnalysisPhase(prev)
  class AnalysisPhase(prev: Phase) extends StdPhase(prev) {

    //TODO dump the DBP (that will alter be handeled by the verification engine)
    //TODO only dump svg in debugmode

    override def run {
      echoPhaseSummary(this)

      //(0) fetch all the classes
      Logger("Plugin", LogInfo, "starting the analysis.")
      Logger("Plugin", LogInfo, "files to process: " + (currentRun.units map (_.source.file.name)).mkString("", ", ", ""))
      currentRun.units foreach (extractClasses(_))
      Logger("Plugin", LogInfo, "classes found: " + classes.keys.mkString("", ", ", ""))

      //TODO PredicateAbstraction
      classes.values foreach (abstractClass(_))

      //merge mergable class (not such a great idea after all)
      //for((s,cls) <- classes) if (classes contains s) cls.nest
      //printClasses(LogDebug)

      //fetch the classes
      val main = classes.values.find(c => isMainClass(c.symbol))
      Logger("Plugin", LogInfo, main map ("Main object is " + _.toString) getOrElse "No Main object found")
      val actors = classes.values.filter(c => isActorClass(c.symbol))
      Logger("Plugin", LogInfo, "actors are " + actors.mkString("", ", ", ""))

      if (main.isEmpty) Logger.logAndThrow("Plugin", LogError, "No main method found")
      for (c <- classes.values) Logger("Plugin", LogInfo, c + " creates " + c.findObjectCreated)

      //some init of global datastructures
      initDispatchTables
      Logger("Plugin", LogDebug, DispatchTable.toStringFull)
      CallGraph.initialize
      Logger("Plugin", LogDebug, CallGraph.toString)

      //build the processes
      Logger("Plugin", LogNotice, allOperations)
      for ((s,c) <- classes) PClasses += (s -> new PClass(c))
      Logger("Plugin", LogDebug, "PClasses created")
      
      PClasses.values foreach (_.processMarkup)
      PClasses.values foreach (_.postMarkup)
      //IO.writeInDocFile(currentRun.units.next.source.file.name + ".classes1.dot", PClasses.toGraphviz("DBP"))
      PClasses.cleanup
      //IO.writeInDocFile(currentRun.units.next.source.file.name + ".classes2.dot", PClasses.toGraphviz("DBP"))
      //PClasses.values foreach (_.expand)
      //IO.writeInDocFile(currentRun.units.next.source.file.name + ".classes3.dot", PClasses.toGraphviz("DBP"))
      PClasses.values foreach (_.updateLiveAt)
      
      //print the classes that will be transformed
      if(Logger("Plugin", LogDebug))
         IO.writeInDocFile(currentRun.units.next.source.file.name + ".classes.dot", PClasses.toGraphviz("DBP"))

      //transforming everything into DBP
      val (init, process) = makeProcess
      extractedDBP = Some(process)
      initState = Some(init)

      Logger("Plugin", LogDebug, "system had " + process.transitions.size + " transitions.")
      //Logger("Plugin", LogDebug, Misc.docToString(process.toGraphvizDoc("DBP")))
      //Console.println( Misc.docToString(process.toGraphviz("DBP")))
      //val out = SysCmd.execWithInputAndGetOutput(Array("dot", "-Tsvg"), Nil, Misc.docToString(process.toGraphviz("DBP")))
      //out match {
      //  case Left(svg) => IO.storeInFile(currentRun.units.next.source.file.name + ".svg", svg)
      //  case Right(code) => Logger("Plugin", LogError, "dot returned " + code)
      //}
      if(Logger("Plugin", LogDebug)) {
        IO.writeInDocFile(currentRun.units.next.source.file.name + ".trs.dot", process.toGraphviz("DBP"))
        IO.writeInDocFile(currentRun.units.next.source.file.name + ".conf.dot", init.toGraphvizDoc("DBP"))
      }

      /* TODO (big picture) Things to do (not necessarily in order)
       * (*) figure out what we can handle
       * (*) preprocessing:
       *    - identifying actor related operations and collection,
       *    - inlining of non recursive method,
       *    - predicate abstraction,
       *    - compatction of automaton:
       *      parts without actor related operation are reduced to one edge.
       *      For parts with loop and recursive methods needs to create verification condition for termination.
       *    - system bootstraping,
       *    - ...
       * (*) CEGAR loop:
       *    - send everyhing to the backend,
       *    -> safe. No bug found.
       *    -> trace -> spurious or real -> refine.
       */

      //TODO how to encode inheritence and object orientation into a pi-cal model ?
      //needs to introduce a dispatch table:
      //name or symbol (maybe form parent) to actual method automaton
      //an actor/thread/process should have a store + pc
      //considering only non recursive method makes it possible to avoid having a stack.
      //however it makes abstraction only possible locally.

      //TODO a predicate object (like topology before) or annotations
      //force the predicates to be class local for the moment
    }

    def apply(unit: CompilationUnit): Unit = {
      Logger.logAndThrow("Plugin", LogInfo, "should be unreachable.")
    }
    
    def extractClasses(unit: CompilationUnit): Unit = {
      val finder = new Traverser {
        override def traverse(tree: Tree) = tree match {
          case impl: ImplDef => classes += (impl.symbol -> Class(impl))
          case _ => super.traverse(tree)
        }
      }
      finder.traverse(unit.body)
    }

  }

  def printCover(cover: _root_.picasso.math.DownwardClosedSet[DBCC]) = {
    import scala.text.Document._
    val docOfBasis = cover.basis.toList.zipWithIndex map { case (t, x) =>
      t.toGraphvizFull("cluster_"+x, "subgraph", "", "c"+x+"_")._1
    }
    val oneDoc = docOfBasis.reduceRight(_ :/: _)
    val doc = "digraph cover {" :: nest(4, empty :/: oneDoc) :/: text("}")
    IO.writeInDocFile(currentRun.units.next.source.file.name + ".cover.dot", doc)
  }

  def computeCover = {
    assert(extractedDBP.isDefined && initState.isDefined)
    val procSimpleForward = new _root_.picasso.model.dbp.DepthBoundedProcess[DBC](extractedDBP.get) with _root_.picasso.analysis.ForwardWithWidening
    val cover = procSimpleForward.computeCover(initState.get)
    //Logger("Plugin", LogDebug, "cover is " + cover)
    Logger("Plugin", LogDebug, "cover 'size' is " + cover.basis.size)
    printCover(cover)
    cover
  }

  def testForPossibleTerminationUsingFullCover = {
    val cover = computeCover
    //val unreachable = _root_.picasso.model.dbp.DepthBoundedConf.empty[DBC] + _root_.picasso.model.dbp.Thread("NEVER")
    //assert(!cover(unreachable))
    val mainFinishes = makeConf(List((unk, msgDest, DBCN("finished"))))
    cover(mainFinishes)
  }
  
  def testForError = {
    assert(extractedDBP.isDefined && initState.isDefined)
    val errorConf = emptyConf + DBCN_Error
    val procSimpleForward = new _root_.picasso.model.dbp.DepthBoundedProcess[DBC](extractedDBP.get) with _root_.picasso.analysis.ForwardWithWidening
    procSimpleForward.forwardCoveringWithTrace(initState.get, errorConf)
  }

}
