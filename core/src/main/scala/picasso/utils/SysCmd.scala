package picasso.utils

import scala.sys.process._

/** executing command as children process */
object SysCmd {

  type ExecResult = (Int, String, String)
  
  //TODO add an option for timeout
  def apply(cmds: Array[String], input: Option[String], addToEnv: (String,String)*): ExecResult = {
    val process = Process(cmds, None, addToEnv:_*)
    val withInput = input match {
      case Some(str) => process #< ( new java.io.ByteArrayInputStream(str.getBytes) )
      case None => process
    }

    val bufferOut = new StringBuffer()
    val bufferErr = new StringBuffer()
    val processLogger = ProcessLogger(bufferOut append _, bufferErr append _)
    Logger("Utils", LogInfo, "Executing "+ cmds.mkString(""," ",""))
    val exitCode = withInput ! processLogger
    (exitCode, bufferOut.toString, bufferErr.toString)
  }
  
  def apply(cmds: Array[String], input: String, addToEnv: (String,String)*): ExecResult =
    apply(cmds, Some(input), addToEnv: _*)

  def apply(cmds: Array[String], addToEnv: (String,String)*): ExecResult =
    apply(cmds, None, addToEnv: _*)
  
  
  def execWithoutOutput(cmds: Array[String], input: Option[String], addToEnv: (String,String)*): Int = {
    val process = Process(cmds, None, addToEnv:_*)
    val withInput = input match {
      case Some(str) => process #< ( new java.io.ByteArrayInputStream(str.getBytes) )
      case None => process
    }
    Logger("Utils", LogInfo, "Executing "+ cmds.mkString(""," ",""))
    withInput ! 
  }
  
  def execRedirectToLogger(cmds: Array[String], input: Option[String], prefix: String, lvl: Level, addToEnv: (String,String)*): Int = {
    val process = Process(cmds, None, addToEnv:_*)
    val withInput = input match {
      case Some(str) => process #< ( new java.io.ByteArrayInputStream(str.getBytes) )
      case None => process
    }
    val processLogger = ProcessLogger(
      out => Logger(prefix, lvl, out),
      err => Logger(prefix, LogWarning, err))
    Logger("Utils", LogInfo, "Executing "+ cmds.mkString(""," ",""))
    withInput ! processLogger
  }

}
