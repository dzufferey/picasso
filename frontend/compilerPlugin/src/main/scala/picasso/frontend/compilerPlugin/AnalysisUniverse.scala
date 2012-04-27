package picasso.frontend.compilerPlugin

import scala.tools.nsc._
import scala.tools.nsc.plugins._
import scala.collection.mutable.{HashMap, ListBuffer}
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger, Level}
import picasso.frontend.compilerPlugin.utils._
import picasso.frontend.compilerPlugin.backend._
import picasso.frontend.compilerPlugin.domains._
import picasso.graph._

abstract class AnalysisUniverse
    extends PluginComponent
    with RawScala
    with TypeUtils
    with FormulaUtils
    with Definitions
    with Extractors
    with PatternUtils
    with TreeUtils
    with SymbolUtils
    with AuxDefinitions
    with PiCode
    with PiCodeTranslator
    with Supported
    with DomainSpecificOperations
    with DBPTranslator
    with Predicates
    with PredicateAbstraction
    //with FunCheckWrapper
{
  import global._
  
  //for digraph of symbols
  type SymGT = GT.ULGT {type V = Symbol}


  //stores the extracted classes (TODO system with phases to make the analysis more modular)
  val classes = new HashMap[Symbol, Class]
  def printClasses(lvl: Level) = for (c <- classes.values) Logger("Plugin", lvl, c.definition.toString)

  /** extract a call graph for the given code (+ overriding edges)  */
  object CallGraph {
    
    //usefull to remove uneeded stuff
    var callGraph: DiGraph[SymGT] = DiGraph.empty[SymGT]
    var allCallableSymbols = Set.empty[Symbol]
    var initialized = false

    def mayBeCalled(s: Symbol) = {
      assert(initialized)
      allCallableSymbols(s)
    }

    override def toString = "All callable methods: " + allCallableSymbols.map(idOfSymbol).mkString("", ", ", "")

    def initialize {
      //make a call graph
      val callGraphEdges1 = (for((_,c) <- classes; (s,m) <- c.methods) yield (s,m.calling)).toList
      val callGraphEdges2 = callGraphEdges1 flatMap { case (s,ms) => ms.toList.map(m => (s,DispatchTable.toUnique.getOrElse(m,m)))}//call the topmost method when possible
      val callGraphEdges3 = callGraphEdges2 ++ DispatchTable.toUnique.iterator.map{case (a,b) => (b,a)}
      callGraph = DiGraph[SymGT](callGraphEdges3)
      val closedCallGraph = callGraph.reflexiveTransitiveClosure
      val main = classes.values.find(c => isMainClass(c.symbol))
      val mainMethod = main.map(_.methods.find(p => isMainMethod(p._1)).get._2.symbol)
      val applyAndCtor = callGraph.vertices.filter(s => s.name == nme.apply || s.isConstructor)
      val stubSymbols = applyAndCtor ++ mainMethod.toList + actMethod
      allCallableSymbols = (Set.empty[Symbol] /: stubSymbols)(_ ++ closedCallGraph(_))
      initialized = true
      //Console.println("callGraphEdges1 " + callGraphEdges1)
      //Console.println("callGraphEdges2 " + callGraphEdges2)
      //Console.println("callGraphEdges3 " + callGraphEdges3)
      //Logger("Plugin", LogDebug, "call graph is: " + callGraph.toGraphviz("CG"))
    }
  }

  /** Keeps an a tree/dag of the inheritance relation */
  lazy val dependencyGraph: DiGraph[SymGT] = {
    val edges = classes.values flatMap ( clazz => {
      val sym = clazz.symbol
      val dependsOn = clazz.parents
      dependsOn map (sym -> _)
    })
    DiGraph[SymGT](edges)
  }
  lazy val transitiveDeptGraph: DiGraph[SymGT] = dependencyGraph.transitiveClosure
  lazy val parentGraph: DiGraph[SymGT] = dependencyGraph.reverse
  lazy val transitiveParentGraph: DiGraph[SymGT] = parentGraph.transitiveClosure
  
  //find some ordering in which classes can be processed.
  lazy val topSortFull = dependencyGraph.topologicalSort
  lazy val topSort = topSortFull filter (classes contains _)

  def hasChild(clazz: Symbol): Boolean = !parentGraph(clazz).isEmpty

  def subTypes(clazz: Symbol): Set[Symbol] = transitiveParentGraph(clazz)

  def superTypes(clazz: Symbol): Set[Symbol] = transitiveDeptGraph(clazz)

  /** The classes tat have no subtypes */
  def BottomClasses: Set[Symbol] = transitiveParentGraph.vertices filter (parentGraph(_).isEmpty)

}
