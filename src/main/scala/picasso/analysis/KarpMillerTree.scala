package picasso.analysis

import picasso.math._
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}

trait KarpMillerTree {
  self : WSTS with WADL =>
  
  sealed abstract class KMTree {
    
    /** Returns the state/limit contained on that node */
    def apply(): S
    
    /** Checks whether the tree covers some state.
     *  Since the tree is cut due to subsumed nodes,
     *  this methods makes only sense if applied at the root. */
    def covers(state: S): Boolean

    def ancestors: Seq[KMTree]

    /** Checks whether a states is covered by some parent */
    def ancestorSmaller(s: S): Seq[KMTree] = {
      ancestors.drop(1).par.filter(t => ordering.lt(t(), s)).seq
    }

    /** inplace modification of the tree */
    def addChildren(tree: KMTree): Unit

    def children: List[KMTree]

    def pathCovering(s: S): Option[List[KMTree]] = {
      if (ordering.lteq(s, this())) Some(List(this))
      else ((None: Option[List[KMTree]]) /: children) ( (acc, child) => acc orElse (child.pathCovering(s) map (this::_)))
    }

    def extractCover: DownwardClosedSet[S] = (DownwardClosedSet(apply()) /: children)( (acc, c) => acc ++ c.extractCover )

    def size: Int = (1 /: children)((acc,ch) => acc + ch.size)

  }

  case class KMRoot(state: S) extends KMTree {
    var _children: List[KMTree] = Nil
    def children = _children
    def addChildren(c: KMTree) = _children = c :: _children
    override def toString = "KMRoot("+state+")" 

    def apply() = state
    def covers(s: S) = ordering.lteq(s, state) || (children exists (_ covers s))
    def ancestors: Seq[KMTree] = Seq(this)
  }
  
  case class KMNode(parent: KMTree, by: T, state: S, acceleratedFrom: List[KMTree]) extends KMTree {
    var _children: List[KMTree] = Nil
    def children = _children
    def addChildren(c: KMTree) = _children = c :: _children
    override def toString = "KMNode("+state+")"

    def apply() = state
    def covers(s: S) = ordering.lteq(s, state) || (children exists (_ covers s))
    def ancestors: Seq[KMTree] = this +: parent.ancestors
  }

  object TreePrinter {

    def add(s: StringBuilder, t: KMTree, indent: Int): Unit = {
      s append ((0 until indent) map ( _ => " ")).mkString("","","")
      s append t
      s append "\n"
      t.children foreach (add(s,_,indent+2))
    }

    def print(t: KMTree) = {
      val string = new StringBuilder()
      add(string, t, 0)
      string.toString
    }

  }

  var time = java.lang.System.currentTimeMillis
  def logIteration(tree: KMTree, current: KMTree, cover: DownwardClosedSet[S]) {
    val newTime = java.lang.System.currentTimeMillis
    if (newTime - time > 10000) {
      Logger("Analysis", LogInfo, "KarpMillerTree: tree has size " + tree.size + ",\tcover has size " + cover.size + ",\t current branch depth " + current.ancestors.size)
      Logger("Analysis", LogDebug, "KarpMillerTree: cover is " + cover)
      time = newTime
    }
  }

  def buildTree(initState: S): KMTree = {
    val root = KMRoot(initState)
    //In Theory, a DFS should be the fastest way to saturate the system, so ...
    //On the side, maintains a (downward-closed) covering set to check for subsumption
    def build(current: KMTree, cover: DownwardClosedSet[S]): DownwardClosedSet[S] = {
      logIteration(root, current, cover)
      if (cover(current())) {
        cover //already subsumed
      } else {
        val newCover = cover + current()
        val possible = transitions.filter(_ isDefinedAt current())//TODO par, or use post from WADL
        (newCover /: possible)((acc, t) => {
          val cs = t(current()).toList.map( s => {
            val acceleratedFrom = current.ancestorSmaller(s)
            val s2 = (s /: acceleratedFrom)( (bigger,smaller) => widening(smaller(), bigger))
            KMNode(current, t, s2, acceleratedFrom.toList)
          })
          (acc /: cs)( (acc2, c) => {
            current.addChildren(c)
            build(c, acc2)
          })
        })
      }
    }
    build(root, DownwardClosedSet.empty[S]) //discard the cover
    Logger("Analysis", LogDebug, "KMTree: final tree is\n" + TreePrinter.print(root))
    root
  }

  private def toTrace(nodes: List[KMTree]): TransfiniteTrace[S,T] = {
    //TODO can the list have nested acceleration ? how to flatten them ?
    //The KMTree should finish only on flattable system, so flattening must be possible.
    //outermost to innermost is needed for WSTS which are not strongly compatible.
    //1 identifies the loop by pair (start, end)
    //2 unfoldind (to preserve strictness) depends on how much the outer loops will consumes ...

    //this version does not handle nested loops
    val rawLoops = nodes flatMap (n => n match {
      case KMNode(_, _, _, acceleratedFrom) => List((n, acceleratedFrom))
      case _ => Nil
    })
    //raw loops are already ordered by loop ending.
    val nodesArray = Array(nodes:_*)
    def findIndex(n: KMTree) = nodesArray indexWhere (_ == n)
    def findConfig(i: Int) = nodesArray(i)()
    def path(from: Int, until: Int): Seq[T] = nodesArray.slice(from+1, until+1) map { 
      case KMNode(_, by, _, _) => by
      case _ => sys.error("KMTree: root in a path")
    }
    val rawIndexedLoops = rawLoops map { case (end, starts) => (findIndex(end), starts map findIndex) }
    val pathes = rawIndexedLoops map { case (end, starts) =>
      val pathes = starts map (path(_,end))
      Pair(end, pathes map (p => Accelerate(p.toList)))
    }
    val finalPath = nodesArray.zipWithIndex flatMap {
      case (KMNode(_, by, _, acceleratedFrom), idx) =>
        Normal(List(by)) :: (pathes find (_._1 == idx) map (_._2) getOrElse Nil)
      case (KMRoot(_), idx) => Nil
    }
    val init = nodesArray(0)()
    val emptyTrace: TransfiniteTrace[S,T] = TransfiniteTrace.empty(DownwardClosedSet(init))
    val revTrace = ( emptyTrace /: finalPath)( (trace, w) => trace.prepend(postCover(trace.start, w), w) )
    revTrace.reverse
  }
  
  def forwardCoveringWithTrace(initState: S, targetState: S): Option[TransfiniteTrace[S,T]] = {
    //TODO stop early
    val tree = buildTree(initState)
    tree.pathCovering(targetState) map toTrace
  }

  def forwardCovering(initState: S, targetState: S): Boolean = {
    //TODO replace be forwardCoveringWithTrace(initState, targetState).isDefined
    val tree = buildTree(initState)
    tree.covers(targetState)
  }
  
  def computeCover(initState: S) = {
    val tree = buildTree(initState)
    tree.extractCover
  }

}
