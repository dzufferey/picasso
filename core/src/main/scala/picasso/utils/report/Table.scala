package picasso.utils.report

class Table(title: String, headers: => Iterable[String], rows: => Iterable[Iterable[String]]) extends Item(title) {

  def toText(writer: java.io.BufferedWriter) {
    //TODO pretty printing
    sys.error("TODO")
    //writer.write(txt); writer.newLine
  }

  def toHtmlInner(writer: java.io.BufferedWriter) = {
    sys.error("TODO")
    //writer.write(html); writer.newLine
  }

}
