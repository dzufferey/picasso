package picasso.model.dbp

import picasso.graph._


class Thread[State](val state: State, val depth: Int) 
extends VertexLike[Thread[State]] {
  override def toString = super.toString + "-" + label.toString
  override def clone = Thread[State](state, depth)
  def ++ = Thread[State](state, depth + 1)
  def -- = Thread[State](state, depth - 1)
  def setDepth(d: Int) = Thread[State](state, d)
  def label = (state, depth)
}

object Thread {
  def apply[State](state: State, depth: Int = 0) : Thread[State] = {
    new Thread(state, depth)
  }
}

trait DBCT extends GT {
  type State
  type V = Thread[State]
  type VL = (State, Int)
}

