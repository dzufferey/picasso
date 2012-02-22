package picasso.utils.report

import java.io.{BufferedWriter, PrintWriter, OutputStreamWriter, FileOutputStream}

class Report(title: String) extends List(title) {

  def htmlHeader(writer: BufferedWriter) {
    writer.write("<!DOCTYPE HTML>"); writer.newLine
    writer.write("<html>"); writer.newLine
    writer.write("<head>"); writer.newLine
    writer.write("    <meta charset=\"utf-8\">"); writer.newLine
    writer.write("    <title>Analysis report for "+title+"</title>"); writer.newLine
    writer.write("</head>"); writer.newLine
    writer.write("<body>"); writer.newLine
  }

  def htmlFooter(writer: BufferedWriter) {
    writer.write("</body>"); writer.newLine
    writer.write("</html>"); writer.newLine
  }

  def htmlTOC(writer: BufferedWriter) {
    val toc = new TOC(this)
    toc.toHtml(writer)
  }
  
  def makeConsoleReport {
    val writer = new BufferedWriter(new PrintWriter(Console.out))
    toText(writer)
    writer.flush
  }
  
  def makeHtmlReport(fileName: String) = {
    val fileOut = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(fileName)))
    htmlHeader(fileOut)
    toHtml(fileOut)
    htmlFooter(fileOut)
    fileOut.close
  }

}
