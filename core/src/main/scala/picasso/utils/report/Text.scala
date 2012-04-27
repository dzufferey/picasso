package picasso.utils.report

class Text(title: String, content: String) extends Item(title) {

  def toText(writer: java.io.BufferedWriter) = sys.error("TODO")

  def toHtmlInner(writer: java.io.BufferedWriter) = {
    writer.write("<p>")
    val escaped = org.apache.commons.lang3.StringEscapeUtils.escapeHtml4(content)
    writer.write(escaped)
    writer.write("</p>")
    writer.newLine
  }

}
