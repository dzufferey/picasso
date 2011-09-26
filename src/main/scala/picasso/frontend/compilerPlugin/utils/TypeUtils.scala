package picasso.frontend.compilerPlugin.utils

import scala.tools.nsc.symtab.Flags._
import scala.tools.nsc.Global
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}

trait TypeUtils {

  val global: Global

  import global._
  import global.definitions._

  /** Checks equality of overloaded symbols
   * @param over a symbol with overloaded type (method)
   * @param s symbol to compare
   */
  def checkOverloadedType(over: Symbol, s: Symbol): Boolean = {
    over.alternatives contains s
  }

  /** Checks if the class owning a symbol is a subtype of some other class.
   * @param sym the symbol corresponding to the class or one of its fields/methods
   * @param of a list of class symbol
   */
  def checkForSubtype(sym: Symbol, of: List[Symbol]): Boolean = {
    if(sym.isClass) of exists (sym.tpe <:< _.tpe)
    else if(sym.isPackage) false //too far
    else checkForSubtype(sym.owner, of)
  }
  def checkForSubtype(sym: Symbol, of: Symbol): Boolean = checkForSubtype(sym, List(of))
  
  /**
   * @param expr an expression of some type ...
   * @param name the requested method
   */
  def classMethod(expr: Tree, name: Name): Symbol = {
    val clazzSymbol = expr.tpe.typeSymbol
    assert(clazzSymbol.isClass)
    getMember(clazzSymbol, name)
  }


  /** Returns the accessor for a given field
   * @param clazz the class containing the field
   * @param name the field's name
   */
  def getAccessorFor(clazz: Symbol, name: Name): Option[Symbol] = {
    assert(clazz.isClass)
    getMember(clazz, name) match {
      case NoSymbol => None
      case s =>
        if (s.isOverloaded) {
          s.tpe match {
            case OverloadedType(pre, alternatives) => alternatives find (_.isGetter)
            case _ => Logger.logAndThrow("Plugin", LogError, "Overloaded symbol has not an OverloadedType.")
          }
        } else if (s.isGetter) Some(s)
        else None
    }
  }
  /** Returns the accessor for a given field
   * @param clazz the type of the class containing the field
   * @param name the field's name
   */
  def getAccessorFor(tpe: Type, name: Name): Option[Symbol] = getAccessorFor(tpe.typeSymbol, name)

}
