package picasso.analysis

import picasso.utils.{LogCritical, LogError, LogWarning, LogNotice, LogInfo, LogDebug, Logger, Misc}
import picasso.model.dbp._

trait DBPTermination[P <: DBCT] extends KarpMillerTree {
  self: DepthBoundedProcess[P] =>

  //(1) compute the cover and extract the transition witnesses
  //(2) using the witnesses create an integer program ...

}
