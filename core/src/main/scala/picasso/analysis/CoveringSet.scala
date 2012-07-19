package picasso.analysis

import picasso.math._

trait CoveringSet {
  self : WSTS with WADL =>
  
  //TODO
  def computeCover(initCover: DownwardClosedSet[S]): DownwardClosedSet[S]
  
  def computeCover(initState: S): DownwardClosedSet[S] = computeCover(DownwardClosedSet(initState))

  //TODO interface for incremental cover computation ...
  //TODO this might be tricky to put the thing in this file due to the mixing composition
  //actually might need to override the transition method so that we can add new stuff

}
