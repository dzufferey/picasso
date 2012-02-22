package picasso.utils.report

class TocEntry(val item: Item, val children: Seq[TocEntry]) {

  def this(item: Item) = this(item, item.children.map(new TocEntry(_)))

  private var pathToRoot: Seq[Int] = Nil
  def setPath(toHere: Seq[Int]) {
    pathToRoot = toHere
    children.zipWithIndex.foreach{ case (c, i) => c.setPath(i +: toHere) }
  }

  lazy val ref = pathToRoot.reverse.mkString("Ref_","_","")
  lazy val number = pathToRoot.reverse.mkString("",".","")
  
  def toText(writer: java.io.BufferedWriter) {
    sys.error("TODO")
  }
  
  def toHtml(writer: java.io.BufferedWriter) {
    writer.write("<li>")
    writer.write("<a href=\"#"+ref+"\"> <span>"+number+"</span> <span>"+item.title+"</span> </a>")
    if( !children.isEmpty) {
      writer.newLine
      writer.write("<ul>"); writer.newLine
      for (c <- children ) c.toHtml(writer)
      writer.write("</ul>"); writer.newLine
    }
    writer.write("</li>"); writer.newLine
  }

}

//an abstraction for table of content
class TOC(report: Report) {

  val entries = new TocEntry(report)
  entries.setPath(Nil)
  
  def toText(writer: java.io.BufferedWriter) {
    sys.error("TODO")
  }

  def toHtml(writer: java.io.BufferedWriter) {
    writer.write("<div id=\"toc\" class=\"toc\">"); writer.newLine
    writer.write("<div id=\"toctitle\" class=\"toctitle\">Contents</div>"); writer.newLine
    writer.write("<ul>"); writer.newLine
    entries.toHtml(writer)
    writer.write("</ul>"); writer.newLine
    writer.write("</div>"); writer.newLine
  }

}
