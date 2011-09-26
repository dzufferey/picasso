package picasso.frontend.compilerPlugin.utils

import scala.tools.nsc.symtab.Flags._
import scala.tools.nsc.Global
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}
import picasso.math.hol.{ClassType => HClassType, Type => HType, Bool => HBool, _}
import picasso.ast._
import picasso.frontend.compilerPlugin.AnalysisUniverse

trait SymbolUtils {
  self: AnalysisUniverse =>

  import global._
  import global.definitions._

  def idOfSymbol(s: Symbol) = s.name.toString.trim + "#" + s.id

  def stringMatchId(str: String)(s: Symbol) = str == idOfSymbol(s)

  /** For a global term symbol points to the class symbol */
  def classTypeSymbol(s: Symbol): Symbol = s.info.typeSymbol

  def IDOfSymbol(s: Symbol) = {
    //Logger("Plugin", LogDebug, "IDOfSymbol: " + symbolDescription(s))
    assert(s.isTerm)
    if (s.isStatic) {
      //in the case of a static symbol: uses the corresponding class
      ID(varOfSymbol(classTypeSymbol(s))) setMode GlobalScope
    } else if (s.owner.isClass) {
      ID(varOfSymbol(s)) setMode ClassScope
    } else {
      assert(s.isLocal);
      ID(varOfSymbol(s)) setMode LocalScope
    }
  }

  /** Find the earliest symbol that the given method overrides */
  def earliestMethod(method: Symbol): Symbol = {
    val possiblyDefinedIn = method.enclClass.ancestors.reverse //in linearization order
    val earliestClass = possiblyDefinedIn.find(method.overriddenSymbol(_) != NoSymbol)
    val earliestSym = earliestClass map (method.overriddenSymbol(_))
    earliestSym getOrElse method
  }

  /** the type returned by a method call. */
  def returning(method: Symbol): Type = {
    assert(method.isMethod)
    method.info.resultType //TODO (actuals: List[Type])
  }

  def symbolDescription(s: Symbol): String = (
    idOfSymbol(s) + ":\n  owned by: " + s.ownerChain.map(idOfSymbol).mkString("", ", ", "") +
    "\n  isTerm " + s.isTerm + ", isType " + s.isType + ", isThisSym " + s.isThisSym +
    "\n  isClass " + s.isClass + ", isModule " + s.isModule +
    "\n  isStaticModule " + s.isStaticModule + ", isModuleClass " + s.isModuleClass +
    "\n  isConstant " + s.isConstant + ", isEffectivelyFinal " + s.isEffectivelyFinal +
    "\n  isStable " + s.isStable + ", isStableClass " + s.isStableClass +
    "\n  isStatic " + s.isStatic + ", isStaticOwner " + s.isStaticOwner +
    "\n  " + "of class :" + idOfSymbol(classTypeSymbol(s))
  )

}
