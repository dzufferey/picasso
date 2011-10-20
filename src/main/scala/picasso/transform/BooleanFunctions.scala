package picasso.transform

import picasso.ast._
import picasso.model.dbp._
import picasso.math._
import picasso.math.hol.{Variable, Bool => HBool}
import picasso.graph._
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}

//boolean interpreted functions
object BooleanFunctions {

  def isBooleanInterpreted(e: Expression): Boolean = e match {
    case Value(Bool(_)) => true
    case ID(v) => true //TODO v.tpe == HBool for the moment assumes it is well typed ...
    case Application("&&", args) => args forall isBooleanInterpreted
    case Application("||", args) => args forall isBooleanInterpreted
    case Application("^", args @ List(a1, a2)) => args forall isBooleanInterpreted
    case Application("!", List(a)) => isBooleanInterpreted(a)
    case Application("==", args @ List(a1, a2)) => args forall isBooleanInterpreted //TODO dangerous without the var type check
    case Application("!=", args @ List(a1, a2)) => args forall isBooleanInterpreted //TODO dangerous without the var type check
    case _ => false
  }

  //choose whether the result is true or false get the possible combinations of values that realize it: maps ID to True/False/_
  def assigns(result: Boolean, partialAssigns: Seq[Map[ID,Boolean]], e: Expression): Seq[Map[ID,Boolean]] = e match {
    case Value(Bool(b)) => if (b == result) partialAssigns else Seq[Map[ID,Boolean]]()
    case id @ ID(_) =>
      partialAssigns flatMap (pa => {
        if (pa contains id) {
          if (pa(id) == result) Seq(pa) else Seq[Map[ID,Boolean]]()
        } else {
          Seq(pa + (id -> result))
        }
      })
    case Application("!", List(a)) => assigns(!result, partialAssigns, a)
    case Application("&&", args) =>
      if (result) (partialAssigns /: args)( (pas, arg) => assigns(true, pas, arg))
      else args flatMap (assigns(false, partialAssigns, _))
    case Application("||", args) => args forall isBooleanInterpreted
      if (!result) (partialAssigns /: args)( (pas, arg) => assigns(false, pas, arg))
      else args flatMap (assigns(true, partialAssigns, _))
    case Application("^", args @ List(a1, a2)) =>
      val a1True = assigns(true, partialAssigns, a1)
      val a1False = assigns(false, partialAssigns, a1)
      if (result) assigns(false, a1True, a2) ++ assigns(true, a1False, a2)
      else assigns(true, a1True, a2) ++ assigns(false, a1False, a2)
    case Application("!=", args @ List(a1, a2)) => //same as Xor
      val a1True = assigns(true, partialAssigns, a1)
      val a1False = assigns(false, partialAssigns, a1)
      if (result) assigns(false, a1True, a2) ++ assigns(true, a1False, a2)
      else assigns(true, a1True, a2) ++ assigns(false, a1False, a2)
    case Application("==", args @ List(a1, a2)) =>
      val a1True = assigns(true, partialAssigns, a1)
      val a1False = assigns(false, partialAssigns, a1)
      if (result) assigns(true, a1True, a2) ++ assigns(false, a1False, a2)
      else assigns(false, a1True, a2) ++ assigns(true, a1False, a2)
    case Any => partialAssigns //Any can be anything
    case err => Logger.logAndThrow("BooleanFunctions", LogError, "Don't know what to do with: " + err)
  }
  
  def assigns(result: Boolean, e: Expression): Seq[Map[ID,Boolean]] =
    assigns(result, Seq(Map.empty[ID,Boolean]), e)
  
  //TODO how to integrate with the rest ??

}
