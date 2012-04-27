package picasso.utils


/** A disjoint set datastructure aka union-find.
 *  TODO extends the appropriate scala interface (Iterable)
 *  TODO an immutable version
 *  TODO a parallel version
 *  TODO performance (if we know the number of nodes in advance, we can use an array which is much faster)
 */
class UnionFind[A]() {

  private class Node(val value: A) {
    var parent: Node = this;
    //var rank = 0;

    def find: Node = {
      if (parent != this) {
        val top = parent.find
        parent = top
        top
      } else {
        this
      }
    }

  }

  private val dict = scala.collection.mutable.HashMap[A, Node]()
  
  private def get(n: A) = {
    if (dict contains n) {
      dict(n)
    } else {
      val node = new Node(n)
      dict += (n -> node)
      node
    }
  }
  
  //adding a new node in the graph (without constraint)
  def +=(n: A) {
    get(n)
  }

  //adding an equality
  def union(n1:A, n2: A) {
    get(n1).find.parent = get(n2).find
  }

  def find(n: A): A = {
    get(n).find.value
  }

  def getEqClasses : Iterable[(A, Iterable[A])] = {
    dict.values.groupBy(_.find).map{ case (k, v) => (k.value, v.map(_.value))}
  }

}
