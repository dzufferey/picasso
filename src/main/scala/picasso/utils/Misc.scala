package picasso.utils

object Misc {

  def docToString(doc: scala.text.Document, width: Int = 80) = {
      val buffer = new java.io.StringWriter
      val writer = new java.io.BufferedWriter( buffer)
      doc.format(width, writer)
      writer.newLine
      writer.close
      buffer.toString
  }

  def quote(str: String) =  "\"" + str.replaceAll("\"", "\\\\\"") + "\""

  def quoteIfFancy(str: String) = if (str matches ".*(\"|\\$|#).*") quote(str) else str

}
