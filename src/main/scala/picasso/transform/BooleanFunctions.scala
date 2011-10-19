package picasso.transform

import picasso.ast._
import picasso.model.dbp._
import picasso.math._
import picasso.math.hol.{Variable, Bool => HBool}
import picasso.graph._
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}

//boolean interpreted functions
trait BooleanFunctions {

  def isBooleanInterpreted(e: Expression): Boolean = e match {
    case Value(Bool(_)) => true
    case ID(v) => true //v.tpe == HBool XXX for the moment assumes it is well typed ...
    case Application("&&", args) => args forall isBooleanInterpreted
    case Application("||", args) => args forall isBooleanInterpreted
    case Application("^", args @ List(a1, a2)) => args forall isBooleanInterpreted
    case Application("!", List(a)) => isBooleanInterpreted(a)
    case _ => false
  }

  //TODO
  //choose whether the result is true or false get the possible combinations of values that realize it: maps ID to True/False/_

}
