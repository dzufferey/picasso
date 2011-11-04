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
      this.ancestorSmallerQuick(s, Set.empty[KMTree])
      //ancestors.drop(1).par.filter(t => ordering.lt(t(), s)).seq
    }

    def ancestorSmallerQuick(s: S, toInclude: Set[KMTree]): Seq[KMTree]

    /** inplace modification of the tree */
    protected var _children: List[KMNode] = Nil
    def children = _children
    def addChildren(c: KMNode) = _children = c :: _children

    def pathCovering(s: S): Option[List[KMTree]] = {
      if (ordering.lteq(s, this())) Some(List(this))
      else ((None: Option[List[KMTree]]) /: children) ( (acc, child) => acc orElse (child.pathCovering(s) map (this::_)))
    }

    def extractCover: DownwardClosedSet[S] = (DownwardClosedSet(apply()) /: children)( (acc, c) => acc ++ c.extractCover )

    def size: Int = (1 /: children)((acc,ch) => acc + ch.size)

  }

  case class KMRoot(state: S) extends KMTree {
    override def toString = "KMRoot("+state+")" 

    def apply() = state
    def covers(s: S) = ordering.lteq(s, state) || (children exists (_ covers s))
    def ancestors: Seq[KMTree] = Seq(this)
    
    def ancestorSmallerQuick(s: S, toInclude: Set[KMTree]): Seq[KMTree] = {
      if (toInclude(this) || ordering.lt(state, s)) Seq(this)
      else Seq[KMTree]()
    }
  }
  
  case class KMNode(parent: KMTree, by: T, state: S, acceleratedFrom: List[KMTree]) extends KMTree {
    override def toString = "KMNode("+state+")"

    def replaceParent(np: KMTree): KMNode = {
      val newThis = KMNode(np, by, state, acceleratedFrom)
      for (c <- children) newThis.addChildren(c.replaceParent(newThis))
      newThis
    }

    def apply() = state
    def covers(s: S) = ordering.lteq(s, state) || (children exists (_ covers s))
    def ancestors: Seq[KMTree] = this +: parent.ancestors
    def ancestorSmallerQuick(s: S, toInclude: Set[KMTree]): Seq[KMTree] = {
      if (toInclude(this)) this +: parent.ancestorSmallerQuick(s, toInclude ++ acceleratedFrom)
      else if (ordering.lt(state, s)) this +: parent.ancestorSmallerQuick(s, toInclude)
      else parent.ancestorSmallerQuick(s, toInclude)
    }
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


  //logging part
  final val logThresold = 10000
  protected var time = java.lang.System.currentTimeMillis
  protected var ticks = 0
  protected def logIteration(tree: KMTree, current: KMTree, cover: DownwardClosedSet[S]) {
    ticks += 1
    val newTime = java.lang.System.currentTimeMillis
    if (newTime - time > logThresold) {
      Logger("Analysis", LogInfo, "KMTree size " + tree.size +
                                  ",\tcover has size " + cover.size +
                                  ",\t current branch depth " + current.ancestors.size +
                                  ",\t ticks " + ticks)
      Logger("Analysis", LogDebug, "Current cover is " + cover)
      time = newTime
    }
  }

  protected def expBackoff[A](seq: Seq[A]): Seq[A] = {
    //Console.println("expBackoff: " + seq.size)
    var count = 2
    val buffer = scala.collection.mutable.Buffer.empty[A]
    var idx = 0
    while (idx < seq.size) {
      buffer += seq(idx)
      idx += 1 + scala.util.Random.nextInt(count)
      count = count * 2
    }
    buffer
  }

  protected def wideningPolicy(current: KMTree, t: T, s: S): KMNode = {
    val acceleratedFrom = current.ancestorSmaller(s)
    val reducedSeq = expBackoff(acceleratedFrom)
    val s2 = (s /: reducedSeq)( (bigger, smaller) => widening(smaller(), bigger))
    KMNode(current, t, s2, acceleratedFrom.toList)
  }

  def buildTree(initState: S): (DownwardClosedSet[S], KMTree) = {
    val startTime = java.lang.System.currentTimeMillis
    val root = KMRoot(initState)
    //In Theory, a DFS should be the fastest way to saturate the system, so ...
    //On the side, maintains a (downward-closed) covering set to check for subsumption
    var cover = DownwardClosedSet.empty[S]
    val stack = scala.collection.mutable.Stack[KMTree](root)
    while (!stack.isEmpty) {
      val current = stack.pop()
      logIteration(root, current, cover)
      if (!cover(current())) {
        cover = cover + current()
        val possible = transitions.filter(_ isDefinedAt current()).par
        val successors = possible.flatMap( t => t(current()).map(t -> _)).par
        //TODO at that point keep only the greatest successors
        val nodes = successors.map { case (t, s) => wideningPolicy(current, t, s) }
        //do this sequentially to avoid data races + use library sorting
        val sortedNodes = current match {
          case KMRoot(_) => nodes.seq
          case KMNode(_, by, _, acceleratedFrom) => 
            val scoredNodes= nodes.map( n => n -> transitionsAffinity(by, n.by) )
            scoredNodes.seq.sortWith( (n1, n2) => n1._2 > n2._2 ).map(_._1)  //TODO what about acceleration
        }
        sortedNodes.foreach( n => {
          current.addChildren(n)
          stack.push(n)
        })
      }
    }
    val endTime = java.lang.System.currentTimeMillis
    Logger("Analysis", LogInfo, "KMTree computed in " + ((endTime - startTime)/1000F) + " sec (cover of size "+cover.size+").")
    Logger("Analysis", LogDebug, "KMTree is\n" + TreePrinter.print(root))
    Logger("Analysis", LogInfo, "Checking fixed-point.")
    if (checkFixedPoint(cover)) {
      Logger("Analysis", LogInfo, "Fixed-point checked.")
    } else {
      Logger("Analysis", LogError, "Fixed-point checking failed.")
    }
    (cover, root)
  }

  //TODO smarter search policy
  //when the depth of the tree increases, it becomes very slow.
  //I am wondering if I should do a periodic restart (keep the current cover, but drop the trees.)

  final val restartThresold = 300000
  protected var sinceRestart = java.lang.System.currentTimeMillis
  protected def start = sinceRestart = java.lang.System.currentTimeMillis
  protected def checkRestart: Boolean = {
    val newTime = java.lang.System.currentTimeMillis
    if (newTime - sinceRestart > restartThresold) {
      Logger("Analysis", LogInfo, "KMTree restarting.")
      sinceRestart = newTime
      true
    } else {
      false
    }
  }

  //TODO the termination of this algorithm is not guarranteed (but should be better in practice)
  //to get termination the restartThresold should be progressively increased
  def buildTreeWithRestart(initState: S): (DownwardClosedSet[S], KMTree) = {
    val startTime = java.lang.System.currentTimeMillis
    val root = KMRoot(initState)
    var cover = DownwardClosedSet.empty[S]
    val stack = scala.collection.mutable.Stack[KMTree]()

    def restart {
      //fold over the tree and collect the parts to process:
      val restartMap = scala.collection.mutable.HashMap[KMRoot, KMTree]()
      val restartStub = scala.collection.mutable.Buffer[KMRoot]()
      while (!stack.isEmpty) {
        val current = stack.pop()
        if (!cover(current())) {
          current match {
            case r @ KMRoot(_) => restartStub += r
            case n @ KMNode(_, _, s, _) =>
              val r = KMRoot(s)
              restartStub += r
              restartMap += (r -> n)
          }
        }
      }
      for (stub <- restartStub) {
        //build from Root in restartStub
        buildFromRoot(stub)
        //glue back to the original tree
        for (original <- restartMap.get(stub); c <- stub.children) {
          original.addChildren(c.replaceParent(original))
        }
      }
    }
    def buildFromRoot(root: KMRoot) {
      Logger("Analysis", LogNotice, "starting from " + root())
      assert(stack.isEmpty)
      stack.push(root)
      start
      while (!stack.isEmpty) {
        if (checkRestart) {
          restart
        } else {
          //like the normal buildTree
          val current = stack.pop()
          logIteration(root, current, cover)
          if (!cover(current())) {
            cover = cover + current()
            val possible = transitions.filter(_ isDefinedAt current()).par
            val successors = possible.flatMap( t => t(current()).map(t -> _)).par
            //at that point keep only the greatest successors
            val successors2 = DownwardClosedSet(successors.map(_._2).seq:_*).basis.toSeq
            val successors3 = successors2.map(b => successors.find(_._2 == b).get).par
            val nodes = successors3.map { case (t, s) => wideningPolicy(current, t, s) }
            //do this sequentially to avoid data races + use library sorting
            val sortedNodes = current match {
              case KMRoot(_) => nodes.seq
              case KMNode(_, by, _, acceleratedFrom) => 
                val scoredNodes= nodes.map( n => n -> transitionsAffinity(by, n.by) )
                scoredNodes.seq.sortWith( (n1, n2) => n1._2 > n2._2 ).map(_._1)  //TODO what about acceleration
            }
            sortedNodes.foreach( n => {
              current.addChildren(n)
              stack.push(n)
            })
          }
        }
      }
    }
    buildFromRoot(root)
    val endTime = java.lang.System.currentTimeMillis
    Logger("Analysis", LogInfo, "KMTree computed in " + ((endTime - startTime)/1000F) + " sec (cover of size "+cover.size+").")
    Logger("Analysis", LogDebug, "KMTree is\n" + TreePrinter.print(root))
    Logger("Analysis", LogInfo, "Checking fixed-point.")
    if (checkFixedPoint(cover)) {
      Logger("Analysis", LogInfo, "Fixed-point checked.")
    } else {
      Logger("Analysis", LogError, "Fixed-point checking failed.")
    }
    (cover, root)
  }



  ////////////////////////////////////////
  // Getting a flat trace from the tree //
  ////////////////////////////////////////

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
    val (_, tree) = buildTreeWithRestart(initState)
    tree.pathCovering(targetState) map toTrace
  }

  def forwardCovering(initState: S, targetState: S): Boolean = {
    //TODO replace be forwardCoveringWithTrace(initState, targetState).isDefined
    val (cover, tree) = buildTreeWithRestart(initState)
    //tree.covers(targetState)
    cover(targetState)
  }
  
  def computeCover(initState: S) = {
    val (cover, tree) = buildTreeWithRestart(initState)
    //tree.extractCover
    cover
  }

}
