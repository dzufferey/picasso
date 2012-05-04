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
  
  def graphvizToSvgDot(dot: String): String = {
    val (code, out, err) = SysCmd(Array("dot", "-Tsvg"), dot)
    if (code == 0) {
      out
    } else {
      Logger("basic", LogWarning, "error running dot (code: "+code+").")
      "<pre>\n" + dot + "\n</pre>"
    }
  }
  
  def graphvizToSvgFdp(dot: String): String = {
    val (code, out, err) = SysCmd(Array("fdp", "-Tsvg", "-GK=1"), dot)
    if (code == 0) {
      out
    } else {
      Logger("basic", LogWarning, "error running fdp (code: "+code+").")
      "<pre>\n" + dot + "\n</pre>"
    }
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

  def safeCall[A,B](fct: A => B, arg: A): Option[B] = {
    try {
      Some(fct(arg))
    } catch {
      case _ => None
    }
  }

  def toBoolean(str: String): Option[Boolean] = safeCall((x: String) => x.toBoolean, str)

  def toInt(str: String): Option[Int] = safeCall((x: String) => x.toInt, str)

  //TODO test
  def allSubLists[A](lst: Seq[A]): Seq[Seq[A]] = lst.headOption match {
    case Some(e) =>
      var sub = allSubLists(lst.tail)
      sub.map( xs => e +: xs ) ++ sub
    case None => Seq(lst)
  }

  def allPartitions[A](lst: Seq[A]): Seq[(Seq[A],Seq[A])] = lst.headOption match {
    case Some(e) =>
      allPartitions(lst.tail).flatMap{ case (left, right) => 
        Seq( (e +: left) -> right, left -> ( e +: right) )
      }
    case None => Seq(lst -> lst)
  }

  //TODO test
  //Cartesian product from many dimensions, but with homogeneous type.
  def cartesianProduct[A](domains: Seq[Seq[A]]): Seq[Seq[A]] = domains.headOption match {
    case Some(lst) => for (xs <- cartesianProduct(domains.tail); x <- lst) yield x +: xs
    case None => domains
  }

}
