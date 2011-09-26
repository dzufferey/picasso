package picasso.utils

/** a, b, c, ..., aa, ab, ... */
class AlphaIterator(capital: Boolean = true) extends Iterator[String] {

  def hasNext = true

  private var counter: Long = 0

  private def iToStr(i: Long): String = {
    var n = i
    var str = ""
    do {
      val rest = (n-1) % 26
      n = (n-1) / 26
      val c = ((if (capital) 'A' else 'a') + rest).toChar
      str = c + str
    } while (n > 0)
    str
  }

  def next: String = {
    counter = counter + 1
    iToStr(counter)
  }
}
