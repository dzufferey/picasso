package picasso.utils.report

  //TODO structure a Report for both console and html output

abstract class Item(val title: String) {
  protected val created = new java.util.Date()

  def children: Seq[Item] = Nil

  def toText(writer: java.io.BufferedWriter)
  def toHtml(writer: java.io.BufferedWriter)

}

