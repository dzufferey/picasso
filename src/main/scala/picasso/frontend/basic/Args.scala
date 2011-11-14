package picasso.frontend.basic

import picasso.utils._

object Args {

  var input: Option[String] = None

  def moreVerbose(l: Level): Level = l match {
    case LogCritical => LogError
    case LogError    => LogWarning
    case LogWarning  => LogNotice
    case LogNotice   => LogInfo
    case LogInfo     => LogDebug
    case LogDebug    => LogDebug
  }
  
  def lessVerbose(l: Level): Level = l match {
    case LogCritical => LogCritical
    case LogError    => LogCritical
    case LogWarning  => LogError
    case LogNotice   => LogWarning
    case LogInfo     => LogNotice
    case LogDebug    => LogInfo
  }
  
  val pf: PartialFunction[List[String], List[String]] = {
    case "-v" :: tail => Logger.setMinPriority(moreVerbose(Logger.getMinPriority)) ; tail
    case "-q" :: tail => Logger.setMinPriority(lessVerbose(Logger.getMinPriority)) ; tail
    case arg :: tail => input = Some(arg); tail
  }

  def apply(args: List[String]): List[String] =
    if (pf isDefinedAt args) apply(pf(args))
    else if (!args.isEmpty) args.head :: apply(args.tail)
    else Nil

}
