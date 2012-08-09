package picasso.frontend.dbpGraph

import picasso.utils._
import picasso.utils.report._
import picasso.model.dbp._
import picasso.analysis._

class Cover(fileName: String, content: String) extends AnalysisCommon("Cover", fileName, content) {


  protected def analysis[P <: picasso.model.dbp.DBCT](_process: DepthBoundedProcess[P], init: DepthBoundedConf[P], target: Option[DepthBoundedConf[P]]): Unit = {
     val process = new DepthBoundedProcess( _process) with KarpMillerTree

     val (cover, tree) = process.computeTree(init)
     
     if (Config.KM_showTree) {
       val treeAsGV = process.TreePrinter.printGraphviz(tree, (t, id, pref) => t().toGraphvizFull(id, "subgraph", "", pref)._1 )
       Logger("dbpGraph", LogInfo, "tree:\n" + treeAsGV )
       report.add( new GenericItem( "KM Tree", treeAsGV, Misc.graphvizToSvgFdp(treeAsGV) ))
     }
     
     Logger("dbpGraph", LogNotice, "cover:\n" + cover)
     val coverReport = new List("Cover")
     for ((c, i) <- cover.zipWithIndex) {
       coverReport.add( new GenericItem(
         "cover element " + i,
         c.toGraphviz("cover"),
         Misc.graphvizToSvgFdp(c.toGraphviz("cover"))
       ))
     }
     report.add(coverReport)

     if (Config.TGCover) {
       val tg = TransitionsGraphFromCover(process, cover)
       val tgAsGV = Misc.docToString(TransitionsGraphFromCover.toGraphviz(tg))
       report.add( new GenericItem( "Transitions graph from cover", tgAsGV, Misc.graphvizToSvgFdp(tgAsGV) ))
     }

     if (Config.interfaceExtraction) {
       val iExtractor = new InterfaceExtraction(process, cover)
       val interface = iExtractor.interface
       report.add(InterfaceExtraction.report(interface))
     }

  }

}
