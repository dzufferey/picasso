package picasso.frontend.compilerPlugin.utils

import scala.tools.nsc.Global
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}
import picasso.utils.Namer
import picasso.math.hol.{ClassType => HClassType, Type => HType, Bool => HBool, _}
import picasso.frontend.compilerPlugin.AnalysisUniverse

trait FormulaUtils {
  self: AnalysisUniverse =>

  val global: Global

  import global._
  import global.definitions._

  def typeOfType(tpe: Type): HType = {
    if (isLiteral(tpe)) {
      //those are the things that will later disappear (expansion) ??
      if (isBoolean(tpe)) HBool
      else if (isString(tpe)) String
      else UnInterpreted(idOfSymbol(tpe.typeSymbol))
    } else {
      //classes: things we might need to keep
      val typeThatMatters = tpe match {
        case RefinedType(parents, _) =>
          //Logger("Plugin", LogDebug, "RefinedType: " + parents)
          //TODO HACK: recode it cleanly
          parents.last
        case tpe => tpe
      }
      val classSym = typeThatMatters.typeSymbol
      val params = tpe.typeArgs
      val classType = HClassType(idOfSymbol(classSym), params map typeOfType)
      if (isActorClass(tpe)) classType.isActor = true
      if (isCaseClass(tpe)) classType.isCase = true
      if (isStdCollection(tpe)) classType.isCollection = true
      if (isModule(tpe)) classType.isModule = true
      //Logger("Plugin", LogDebug, "typeOfType: " + tpe + " -> " + classType + " -> " + tpe.typeSymbol)
      classType
    }
  }

  def typeOfSymbol(s: Symbol): HType = typeOfType(s.info) 

  def varOfSymbol(s: Symbol) = {
    val v = Variable(idOfSymbol(s))
    v.tpe = typeOfSymbol(s)
    v
  }

  object SSA {
    
    def mostRecent(map: Map[Symbol, Symbol], s: Symbol): Symbol = {
      map.get(s) match {
        case Some(s2) => mostRecent(map, s2)
        case None => s
      }
    }

    def fresh(map: Map[Symbol, Symbol], s: Symbol): (Map[Symbol, Symbol], Symbol) = {
      val s2 = mostRecent(map, s)
      val fresh = Namer(s2.name.toString, true) // is true the right way ? 
      val s3 = s2.owner.newValue(s2.pos, fresh).setInfo(s2.info)
      (map + (s2 -> s3), s3)
    }
    
    def makeSubstList(map: Map[Symbol, Symbol]) = {
      val (from, toPartial) = map.toList.unzip
      (from, toPartial.map(s => Ident(mostRecent(map, s)) setType s.info))
    }

    def subst(map: Map[Symbol, Symbol], tree: Tree): Tree = {
      val (from, to) = makeSubstList(map)
      substituteRef(from, to, tree)
    }

    /** Transform a path with Assign into a path in SSA (only ValDef)
     *  Assumes: the values are immutable and that function calls have no side effects.
     *  Assumes: unrolled path (no blocks)
     *  @returns a map ``s_1 becomes s_2'' and the new path
     */
    def apply(path: Iterable[Tree], initMap: Map[Symbol, Symbol] = Map.empty[Symbol, Symbol]): (Map[Symbol, Symbol], Iterable[Tree]) = {
      val buffer = new scala.collection.mutable.ListBuffer[Tree]()
      val becomes = ( initMap /: path )( (acc, stmt) => {
        stmt match {
          case as @ Assign(lhs, rhs) => 
            val rhs2 = subst(acc, rhs)
            val (acc2, s2) = fresh(acc, lhs.symbol)
            buffer += ValDef(s2, rhs2)
            acc2 

          case ap @ Apply(_, _) =>
            Logger("Plugin", LogWarning, "Apply not assigned, side-effect ? " + ap)
            buffer += subst(acc, ap)
            acc
        
          case tree @ (ValDef(_, _, _, _) | Ident(_) | EmptyTree | Literal(_)) =>
            buffer += subst(acc, tree)
            acc
        
          case other => Logger.logAndThrow("Plugin", LogError, "SSA conversion do not support: " + other)
        }
      })
      (becomes, buffer.toList)
    }

  }

}
