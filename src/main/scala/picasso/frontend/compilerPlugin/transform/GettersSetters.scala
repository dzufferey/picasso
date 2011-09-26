package picasso.frontend.compilerPlugin.transform

import scala.tools.nsc._
import scala.tools.nsc.plugins._
import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger}
import picasso.frontend.compilerPlugin.utils._
import picasso.frontend.compilerPlugin._

/** within the one class, the getters and setters can be removed
 *  and replaced by a reference to the appropriate variable.
 */
class GettersSetters(val global: Global, val picasso: PicassoPlugin)
  extends PluginComponent with TreeUtils
{
  import global._
  import global.definitions._

  override val runsRightAfter: Option[String] = None
  override val runsAfter: List[String] = List(picasso.name + ".link")


  val phaseName = picasso.name + ".gettersSetters"
  
  def newPhase(prev: Phase) = new GSPhase(prev)
  
  class GSPhase(prev: Phase) extends StdPhase(prev) {
    
    def apply(unit: CompilationUnit): Unit = {
      val remover = new GSRemover
      remover.transformUnit(unit)
      Logger("Plugin", LogInfo, "GettersSetters result for " + unit.source.file.name + ":\n" + unit.body)
    }

  }
  

  //TODO rather than looking at current class (which is wrong), look for 'this'

  private class GSRemover extends Transformer {
    var classDef: Option[ClassDef] = None //assume no nested classes

    override def transform(tree: Tree): Tree = tree match {
      case cd @ ClassDef(_,_,_,_) =>
        val sym = cd.symbol
        if (!sym.isAbstractClass && !sym.isTrait) {
          val prev = classDef
          classDef = Some(cd)
          val result = super.transform(cd)
          classDef = prev
          result
        } else {
          cd
        }

      case Apply(t @ Select(This(_), _), Nil) if t.hasSymbol && (t.symbol != NoSymbol) && t.symbol.isGetter => 
        assert(currentClass.info.baseClasses contains t.symbol.owner, tree)
        val clazz = currentClass
        val _this = This(clazz) setType clazz.info
        val value = valueOfGetterSetterStructural(classDef.get, t.symbol)
        assert(value != NoSymbol, "valueOfGetterSetter("+clazz+","+t.symbol+")")
        Select(_this, value) setType value.info
      
      case Apply(t @ Select(This(_), _), List(arg)) if t.hasSymbol && (t.symbol != NoSymbol) && t.symbol.isSetter => 
        assert(currentClass.info.baseClasses contains t.symbol.owner, tree)
        val clazz = currentClass
        val _this = This(clazz) setType clazz.info
        val value = valueOfGetterSetterStructural(classDef.get, t.symbol)
        assert(value != NoSymbol, "valueOfGetterSetter("+clazz+","+t.symbol+")")
        val slt = Select(_this, value) setType value.info
        Assign(slt, arg)
      
      case _ =>
        super.transform(tree)
    }

  }

  //TODO compact local variables: this can only be done when there is no risk of interleaving (ok for local vars)

}
