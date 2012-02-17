package picasso.utils.report

class List(title: String) extends Item(title) {
  
  protected val children = scala.collection.mutable.Buffer[Item]()

  def toText(writer: java.io.Writer) = sys.error("TODO")
  def toHtml(writer: java.io.Writer) = sys.error("TODO")

}

