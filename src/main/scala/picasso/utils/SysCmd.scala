package picasso.utils

import java.lang.Process
import java.lang.Runtime

/** executing command as children process */
object SysCmd {
  
  def exec(cmds: Array[String], addToEnv: Iterable[(String,String)]): Process = {
    val it = java.lang.System.getenv.entrySet.iterator
    var env: List[String] = Nil
    while (it.hasNext) {
      val entry = it.next
      env = (entry.getKey + "=" + entry.getValue) :: env
    }
    val toAddNice = addToEnv map (p => p._1 + "=" + p._2)
    val env2 = (env ++ toAddNice).toArray
    Logger("Utils", LogNotice, "Executing "+ cmds.mkString(""," ","") + " with " + toAddNice.mkString("",",",""))
    Runtime.getRuntime().exec(cmds, env2)
  }

  //exec: send data to child, get result from output, returns it.
  //TODO read from both output and error (needs to create 2 Thread ?)
  //TODO add an option for timeout
  //TODO harden that part!!
  def execWithInputAndGetOutput(cmds: Array[String], addToEnv: Iterable[(String,String)], input: Array[Byte]): Either[Array[Byte], Int] = {
    val buffer = Array.ofDim[Byte](10 * 1024 * 1024)
    val result = scala.collection.mutable.ArrayBuffer[Byte]()
    val process = exec(cmds, addToEnv)
    val writer = process.getOutputStream
    val processOutput = new java.io.DataInputStream(process.getInputStream)
    var status = -1
    try {
      writer.write(input)
      writer.close
      var read = processOutput.read(buffer)
      while (read > 0) {
        result ++= buffer.view( 0, read)
        read = processOutput.read(buffer)
      }
    } finally {
      try { processOutput.close } catch {case _ => ()}
      try { status = process.waitFor  } catch {case _ => ()} //TODO Timeout ?
    }
    if (status == 0) Left(result.toArray)
    else Right(status)
  }

  def execWithInputAndGetOutput(cmds: Array[String], addToEnv: Iterable[(String,String)], input: String): Either[Array[Byte], Int] =
    execWithInputAndGetOutput(cmds, addToEnv, input.getBytes)
}
