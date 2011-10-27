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

  def indent(prefix: String, content: String) = {
    val builder = new StringBuilder(content)
    //if the last char is a line return, replace it by a space
    if ((! builder.isEmpty) && (builder(builder.size -1) == '\n')) builder.setLength(builder.size -1)
    var start = 0
    while (start < builder.length && builder.indexOf('\n', start) != -1) {
      val idx = builder.indexOf('\n', start)
      builder.insert(idx+1, prefix)
      start = idx + prefix.length + 1
    }
    prefix + builder
  }

}
