package picasso.utils

//logging facility (i.e. syslog alike)

sealed abstract class Level(msg: String, prio: Int, col: String) {
  def message = msg
  def priority = prio
  def color = col
}
case object LogCritical extends Level("Critical", 32, Console.RED)
case object LogError    extends Level("Error",    16, Console.RED)
case object LogWarning  extends Level("Warning",  8,  Console.YELLOW)
case object LogNotice   extends Level("Notice",   4,  Console.BLUE)
case object LogInfo     extends Level("Info",     2,  Console.RESET)
case object LogDebug    extends Level("Debug",    1,  Console.RESET)

//TODO one logger for all or separated logger ? (Console, file, network, ...)

/** Simple logger that outputs to stdout. */
class Logger {

  private var minPriority = LogNotice.priority
  val disallowed = scala.collection.mutable.HashSet.empty[String]

  def reset = {
    minPriority = LogInfo.priority
    disallowed.clear()
  }
  def getMinPriority = minPriority match {
    case x if x == LogCritical.priority => LogCritical
    case x if x == LogError.priority => LogError
    case x if x == LogWarning.priority => LogWarning
    case x if x == LogNotice.priority => LogNotice
    case x if x == LogInfo.priority => LogInfo
    case x if x == LogDebug.priority => LogDebug
    case p => sys.error("unknown priority ("+p+")")
  }
  def setMinPriority(lvl: Level) = minPriority = lvl.priority
  def setMinPriority(lvl: Int) = minPriority = lvl
  def disallow(str: String) = disallowed += str
  def allow(str: String) = disallowed -= str

  /** Should be dispayed ? */
  def apply(relatedTo: String, lvl: Level): Boolean =
    lvl.priority >= minPriority && !disallowed(relatedTo)

  /** Log a message to the console.
   * @param relatedTo The package/file/class from where this message comes from.
   * @param lvl The priority of the message.
   * @param content The content of the message (evaluated only if needed).
   */
  def apply(relatedTo: String, lvl: Level, content: => String): Unit = synchronized {
    if (apply(relatedTo, lvl)) {
      //when content is on multiple lines, each line should be prefixed.
      val prefix = "[" + lvl.color + lvl.message + Console.RESET + "]" + " @ " + relatedTo + ": " 
      val indented = Misc.indent(prefix, content)
      Console.println(indented)
    }
  }

  /** Log a message and throw an exception with the content. */
  def logAndThrow(relatedTo: String, lvl: Level, content: => String): Nothing = {
    apply(relatedTo, lvl, content)
    Console.flush
    sys.error(content)
  }

}

object Logger extends Logger {
}
