package picasso.model.pn

import picasso.math._
import scala.math.Ordering
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}

sealed abstract class Tokens
case class  Normal(value: Int) extends Tokens {
  override def toString = value.toString
}
case object Omega extends Tokens {
  override def toString = "ω"
}

class PNState(s: Array[Tokens]) {

  def this(s: Array[Int]) = this(s map (Normal(_): Tokens))

  def size = s.size
  override def clone = new PNState(s.clone)
  
  def apply(i: Int) = s(i)
  def get(i: Int) = s(i) match {
    case Normal(v) => v
    case Omega => sys.error("PNState.get: found Omega")
  }
  def update(i:Int, v: Int) = s.update(i,Normal(v))
  def update(i:Int, v: Tokens) = s.update(i,v)
  def indices = s.indices

  override def toString = s.mkString("(",",",")")
}

object limitConfigurationOrdering extends WellPartialOrdering[PNState] {
  val incomparable = 123456789

  def compareTokens(t1: Tokens, t2: Tokens) = (t1,t2) match {
    case (Omega, Omega) => 0
    case (Omega, _) => 1
    case (_, Omega) => -1
    case (Normal(v1), Normal(v2)) => Ordering.Int.compare(v1,v2)
  }

  def tryCompare(p1: PNState, p2: PNState): Option[Int] = {
    if (p1.size != p2.size) {
      None
    } else {
      val compared = p1.indices.foldLeft(0)( (acc, idx) => {
        if (acc == incomparable) incomparable else {
          val c = compareTokens(p1(idx), p2(idx))
          (acc,c) match {
            case (1,1) | (1,0) | (0,1) => 1
            case (0,0) => 0
            case (-1,-1) | (-1,0) | (0,-1) => -1
            case _ => incomparable
          }
        }
      })
      if (compared == incomparable) None else Some(compared)
    }
  }

  def lteq(p1: PNState, p2: PNState): Boolean = {
    val comp = tryCompare(p1,p2).getOrElse(incomparable)
    comp == -1 || comp == 0
  }
}


/** Petri Net Transition*/
class PNTransition(val consume: List[(Int,Int)], val produce: List[(Int,Int)]) extends Transition[PNState] {
  lazy val minPNSize = consume.foldLeft(produce.foldLeft(0)(_ max _._1))(_ max _._1)

  def apply(state: PNState): Set[PNState] = {
    val state2 = state.clone
    consume foreach ( x => state2(x._1) match {
      case Normal(v) => state2.update(x._1, v - x._2)
      case Omega => ()
    })
    produce foreach ( x => state2(x._1) match {
      case Normal(v) => state2.update(x._1, v + x._2)
      case Omega => ()
    })
    scala.collection.immutable.Set(state2)
  }

  def reverse: PNTransition = new PNTransition(produce, consume)

  def isDefinedAt(state: PNState): Boolean =
    (state.size > minPNSize) && (consume forall ( x => state(x._1) match {
      case Normal(v) => v >= x._2
      case Omega => true
  }))

  override def toString = consume.mkString("",",","") + " -> " + produce.mkString("",",","")
}

class PetriNet(trs: List[PNTransition]) extends WSTS with Pre with PredBasis with WADL {

  type S = PNState
  implicit val ordering: WellPartialOrdering[S] = limitConfigurationOrdering

  type T = PNTransition
  def transitions = trs

  def pre(s: S, t: T): Set[S] = post(s, t.reverse)

  def predBasis(s: UpwardClosedSet[S], t: T): UpwardClosedSet[S] = {
    //This is going backward. by the upward closure semantic, the transition is always applicable.
    //take procuced token whenever possible, always add consummed tokens
    def relaxedOneStep(s: S): S = {
      val s2 = s.clone
      t.produce foreach ( x => s2.update(x._1, 0 max (s2.get(x._1) - x._2)))
      t.consume foreach ( x => s2.update(x._1, s2.get(x._1) + x._2))
      s2
    }
    (UpwardClosedSet.empty[S] /: s)(_  + relaxedOneStep(_))
  }

  def tryAcceleratePair(smaller: S, bigger: S): Option[S] = {
    try {
      def token(t1: Tokens, t2: Tokens): Tokens = (t1,t2) match {
        case (Omega, Omega) => Omega
        case (Omega, _) => sys.error("PetriNet.widening: smaller is bigger than bigger")
        case (_, Omega) => Omega
        case (Normal(v1), Normal(v2)) if v1 < v2 => Omega
        case (Normal(v1), Normal(v2)) if v1 == v2 => Normal(v1)
        case (Normal(v1), Normal(v2)) => sys.error("PetriNet.widening: smaller is bigger than bigger")
      }
      assert(smaller.size == bigger.size)
      val _new = bigger.clone
      smaller.indices.foreach( idx => _new.update(idx, token(smaller(idx), bigger(idx))))
      Some(_new)
    } catch {case e: Exception => None}
  }

  private def processList(s: S, lst: List[T]): DownwardClosedSet[S] = postCover(DownwardClosedSet(s), picasso.math.Normal(lst))

  
  override def accelerate(states: DownwardClosedSet[S], transitions: List[T]): DownwardClosedSet[S] = {
    def pairs = ((states.basis map ( x => (x, processList(x, transitions)))) filter (!_._2.isEmpty)) map ( p => (p._1,p._2.head))
    def increasingPairs = pairs filter ( p => ordering.lt(p._1, p._2))
    def newBasis = increasingPairs map ( p => widening(p._1, p._2))
    DownwardClosedSet.fromParBasis(newBasis)
  }

}
