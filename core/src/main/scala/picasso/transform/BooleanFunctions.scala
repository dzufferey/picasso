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
    case ID(v) => v.tpe == HBool
    case Application("random", Nil) => true
    case Application("&&", args) => args forall isBooleanInterpreted
    case Application("||", args) => args forall isBooleanInterpreted
    case Application("^", args @ List(a1, a2)) => args forall isBooleanInterpreted
    case Application("!", List(a)) => isBooleanInterpreted(a)
    case Application("==", args @ List(a1, a2)) => args forall isBooleanInterpreted
    case Application("!=", args @ List(a1, a2)) => args forall isBooleanInterpreted
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
    case Application("random", Nil) => partialAssigns 
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
  

  def groundTermSimplificationOneLevel(e: Expression): Expression = e match {
    case Application("&&", args) =>
      val args2 = args.filter{ case Value(Bool(true)) => false; case _ => true}
      if (args2.isEmpty) Value(Bool(true))
      else if (args2 exists { case Value(Bool(false)) => true; case _ => false}) Value(Bool(false))
      else Application("&&", args2) 

    case Application("||", args) => 
      val args2 = args.filter{ case Value(Bool(false)) => false; case _ => true}
      if (args2.isEmpty) Value(Bool(false))
      else if (args2 exists { case Value(Bool(true)) => true; case _ => false}) Value(Bool(true))
      else Application("||", args2) 
    
    case Application("^", List(Value(Bool(b)),e2 @ ID(_))) => if (!b) e2 else Application("!", List(e2))
    case Application("^", List(e1 @ ID(_),Value(Bool(b)))) => if (!b) e1 else Application("!", List(e1))
    case Application("^", List(Value(Bool(b1)),Value(Bool(b2)))) => Value(Bool(b1 != b2))
    
    case Application("==", List(Value(Bool(b)),e2 @ ID(_))) => if (b) e2 else Application("!", List(e2))
    case Application("==", List(e1 @ ID(_),Value(Bool(b)))) => if (b) e1 else Application("!", List(e1))
    case Application("==", List(Value(Bool(b1)),Value(Bool(b2)))) => Value(Bool(b1 == b2))
    
    case Application("!=", List(Value(Bool(b)),e2 @ ID(_))) => if (!b) e2 else Application("!", List(e2))
    case Application("!=", List(e1 @ ID(_),Value(Bool(b)))) => if (!b) e1 else Application("!", List(e1))
    case Application("!=", List(Value(Bool(b1)),Value(Bool(b2)))) => Value(Bool(b1 != b2))
    
    case Application("!", List(Value(Bool(b)))) => Value(Bool(!b))
    case other => other
  }

  def groundTermSimplification(e: Expression): Expression = e match {
    case Application(fct, args) => groundTermSimplificationOneLevel(Application(fct, args map groundTermSimplification))
    case Tuple(values) => Tuple(values map groundTermSimplification)
    case other => groundTermSimplificationOneLevel(other)
  }

}
