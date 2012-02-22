package picasso.utils.report

class List(title: String) extends Item(title) {
  
  protected val _children = scala.collection.mutable.Buffer[Item]()

  override def children = children

  def add(element: Item) {
    _children += element
  }

  def toText(writer: java.io.BufferedWriter) = sys.error("TODO")
  def toHtml(writer: java.io.BufferedWriter) = sys.error("TODO")

}

