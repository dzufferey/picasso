package picasso.ast

//TODO instead of using the PI prefix for Zero and ProcessID, should this be in its own package ?

import scala.collection.immutable.TreeSet
import scala.collection.immutable.{TreeMap, Map}
import scala.collection.Set

//pi-calculus AST
sealed abstract class PiProcess {
  def freeNames: Set[String]
  def boundNames: Set[String]
  private lazy val n = freeNames ++ boundNames
  def names: Set[String] = n
  
  //this version does not check for name capture (i.e. replacing a free name by a bound name).
  def alphaUnsafe(map: Map[String, String]): PiProcess //TODO PiProcessLike to return the same type ?
  //this version checks for name capture.
  def alpha(map: Map[String, String]): PiProcess
  //replaces both free and bound names
  def alphaAll(map: Map[String, String]): PiProcess
  
  def isObservablePrefix(name: String): Boolean
}

case class Composition(processes: List[PiProcess]) extends PiProcess {
  private lazy val fn = (TreeSet.empty[String] /: processes)( _ ++ _.freeNames)
  def freeNames: Set[String] = fn
  private lazy val bn = (TreeSet.empty[String] /: processes)( _ ++ _.boundNames)
  def boundNames: Set[String] = bn
  def alphaUnsafe(map: Map[String, String]): PiProcess = Composition(processes map (_.alphaUnsafe(map)))
  def alpha(map: Map[String, String]): PiProcess = Composition(processes map (_.alpha(map)))
  def alphaAll(map: Map[String, String]): PiProcess = Composition(processes map (_.alphaAll(map)))
  def isObservablePrefix(name: String): Boolean = processes exists (_.isObservablePrefix(name))
}

case class Choice(processes: List[PiProcess]) extends PiProcess {
  private lazy val fn = (TreeSet.empty[String] /: processes)( _ ++ _.freeNames)
  def freeNames: Set[String] = fn
  private lazy val bn = (TreeSet.empty[String] /: processes)( _ ++ _.boundNames)
  def boundNames: Set[String] = bn
  def alphaUnsafe(map: Map[String, String]): PiProcess = Choice(processes map (_.alphaUnsafe(map)))
  def alpha(map: Map[String, String]): PiProcess = Choice(processes map (_.alpha(map)))
  def alphaAll(map: Map[String, String]): PiProcess = Choice(processes map (_.alphaAll(map)))
  def isObservablePrefix(name: String): Boolean = processes exists (_.isObservablePrefix(name))
}

case class Restriction(name: String, process: PiProcess) extends PiProcess {
  private lazy val fn = process.freeNames - name
  def freeNames: Set[String] = fn
  private lazy val bn = process.boundNames + name
  def boundNames: Set[String] = bn
  def alphaUnsafe(map: Map[String, String]): PiProcess = Restriction(name, process.alphaUnsafe(map - name))
  def alpha(map: Map[String, String]): PiProcess = {
    val imageSet = Set.empty[String] ++ map.values
    val conflicting = (boundNames intersect imageSet) -- freeNames //names that are both bound+free will be dealt later
    val subst = PiProcess.freshNamesFor(this, imageSet, conflicting)
    if (!conflicting.isEmpty) this.alphaAll(subst).alpha(map)
    else Restriction(name, process.alphaUnsafe(map - name))
  }
  def alphaAll(map: Map[String, String]): PiProcess = Restriction(map.getOrElse(name, name), process.alphaAll(map))
  def isObservablePrefix(n: String): Boolean = if (n == name) false else process isObservablePrefix n
}

case class Repetition(process: PiProcess) extends PiProcess {
  def freeNames: Set[String] = process.freeNames
  def boundNames: Set[String] = process.boundNames
  def alphaUnsafe(map: Map[String, String]): PiProcess = Repetition(process.alphaUnsafe(map))
  def alpha(map: Map[String, String]): PiProcess = Repetition(process.alpha(map))
  def alphaAll(map: Map[String, String]): PiProcess = Repetition(process.alphaAll(map))
  def isObservablePrefix(name: String): Boolean = process isObservablePrefix name
}

case class InputPrefix(channel: String, args: List[String], process: PiProcess) extends PiProcess {
  private lazy val fn = (process.freeNames /: args)(_ - _) + channel
  def freeNames: Set[String] = fn
  private lazy val bn = (process.boundNames /: args)(_ + _)
  def boundNames: Set[String] = bn
  def alphaUnsafe(map: Map[String, String]): PiProcess = {
    val channel2 = map.getOrElse(channel, channel)
    val map2 = map -- args
    InputPrefix(channel2, args, process.alphaUnsafe(map2))
  }
  def alpha(map: Map[String, String]): PiProcess = {
    val imageSet = Set.empty[String] ++ map.values
    val conflicting = (boundNames intersect imageSet) -- freeNames
    assert(!(args contains channel))//otherwise problem
    val subst = PiProcess.freshNamesFor(this, imageSet, conflicting)
    if (!conflicting.isEmpty)this.alphaAll(subst).alpha(map)
    else {
      val channel2 = map.getOrElse(channel, channel)
      val map2 = map -- args
      InputPrefix(channel2, args, process.alpha(map2))
    }
  }
  def alphaAll(map: Map[String, String]): PiProcess = {
    val channel2 = map.getOrElse(channel, channel)
    val args2 = args map ( n => map.getOrElse(n, n))
    InputPrefix(channel2, args2, process.alphaAll(map))
  }
  def isObservablePrefix(name: String): Boolean = name == channel
}

case class OutputPrefix(channel: String, args: List[String], process: PiProcess) extends PiProcess {
  private lazy val fn = (process.freeNames /: args)(_ + _) + channel
  def freeNames: Set[String] = fn
  def boundNames: Set[String] = process.boundNames
  def alphaUnsafe(map: Map[String, String]): PiProcess = {
    val channel2 = map.getOrElse(channel, channel)
    val args2 = args map ( n => map.getOrElse(n, n))
    OutputPrefix(channel2, args2, process.alphaUnsafe(map))
  }
  def alpha(map: Map[String, String]): PiProcess = {
    val channel2 = map.getOrElse(channel, channel)
    val args2 = args map ( n => map.getOrElse(n, n))
    OutputPrefix(channel2, args2, process.alpha(map))
  }
  def alphaAll(map: Map[String, String]): PiProcess = {
    val channel2 = map.getOrElse(channel, channel)
    val args2 = args map ( n => map.getOrElse(n, n))
    OutputPrefix(channel2, args2, process.alphaAll(map))
  }
  def isObservablePrefix(name: String): Boolean = name == channel
}

case object PiZero extends PiProcess {
  def freeNames: Set[String] = TreeSet.empty[String]
  def boundNames: Set[String] = TreeSet.empty[String]
  def alphaUnsafe(map: Map[String, String]): PiProcess = PiZero
  def alpha(map: Map[String, String]): PiProcess= PiZero
  def alphaAll(map: Map[String, String]): PiProcess= PiZero
  def isObservablePrefix(name: String): Boolean = false
}

case class PiProcessID(id: String, args: List[String]) extends PiProcess {
  def freeNames: Set[String] = (TreeSet.empty[String] /: args)(_ + _)
  def boundNames: Set[String] = TreeSet.empty[String]
  def alphaUnsafe(map: Map[String, String]): PiProcess = PiProcessID(id, args map ( n => map.getOrElse(n, n)))
  def alpha(map: Map[String, String]): PiProcess = PiProcessID(id, args map ( n => map.getOrElse(n, n)))
  def alphaAll(map: Map[String, String]): PiProcess = PiProcessID(id, args map ( n => map.getOrElse(n, n)))
  def isObservablePrefix(name: String): Boolean = false
}

object PiProcess {

  def isInputPrefix(p: PiProcess) = p match {
    case InputPrefix(_,_,_) => true
    case _ => false
  }

  def isOutputPrefix(p: PiProcess) = p match {
    case OutputPrefix(_,_,_) => true
    case _ => false
  }

  //returns a substitution tha mape to names that does not appears in p
  def freshNamesFor(p: PiProcess, toAvoid: Set[String], conflicting: Set[String]): Map[String, String] = {
    val notIn = toAvoid ++ conflicting
    val it = new picasso.utils.AlphaIterator
    def nextFree: String = {
      val str = it.next
      if (notIn(str)) nextFree
      else str
    }
    (TreeMap.empty[String,String] /: conflicting )(_ + Pair(_, nextFree))
  }
  
}
