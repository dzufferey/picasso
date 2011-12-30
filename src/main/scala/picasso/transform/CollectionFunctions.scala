package picasso.transform

import picasso.ast._
import picasso.model.dbp._
import picasso.math._
import picasso.math.hol.{Variable, Bool => HBool}
import picasso.graph._
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}

//interpreted functions that manipulate collections
object CollectionFunctions {

  //TODO
  def isCollectionInterpreted(e: Expression): Boolean = e match {
    case EmptySet() => true
    case SetIsEmpty(_) => true
    case SetAdd(_,_) => true
    case SetMinus(_, _) => true
    case SetChoose(_) => true
    case SetPick(_) => true
    case SetCopy(_) => true
    case _ => false
  }

}
