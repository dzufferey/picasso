package picasso.utils.report

  //TODO structure a Report for both console and html output

abstract class Item(title: String) {
  protected val created = new java.util.Date()

  def toText(writer: java.io.Writer)
  def toHtml(writer: java.io.Writer)

  //TODO TOC generation ?

}

