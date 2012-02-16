package picasso.utils

import scala.text.Document
import java.io._

object IO {

  def storeInFile(file: File, data: Array[Byte]): Unit = {
    val fileOut = new DataOutputStream( new FileOutputStream(file))
    fileOut.write(data, 0, data.length)
    fileOut.close
  }

  def storeInFile(file: String, data: Array[Byte]): Unit = storeInFile(new File(file), data)

  def storeInTempFile(prefix: String, suffix: String, uploadDirectory: File, data: Array[Byte]) = {
    val storage = java.io.File.createTempFile(prefix, suffix, uploadDirectory)
    storeInFile(storage, data)
    storage
  }

  def writeInFile(file: File, data: String): Unit = {
    val fileOut = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(file)))
    fileOut.write(data)
    fileOut.close
  }
  
  def writeInFile(file: String, data: String): Unit = writeInFile(new File(file), data)
  
  def writeInDocFile(file: File, data: Document, width: Int): Unit = {
    val fileOut = new BufferedWriter(new OutputStreamWriter(new FileOutputStream(file)))
    data.format(width, fileOut)
    fileOut.close
  }
  
  def writeInDocFile(file: String, data: Document, width: Int = 80): Unit =
    writeInDocFile(new File(file), data, width) 

  //TODO the append to file version
  //...

  def readTextFile(file: String): String = {
    val fileIn = new BufferedReader(new FileReader(file))
    val builder = new StringBuilder(1000)
    while(fileIn.ready) {
      builder ++= fileIn.readLine + "\n"
    }
    fileIn.close
    builder.toString
  }

  def readStdin: String = {
    val read = new scala.collection.mutable.StringBuilder
    var line = scala.Console.in.readLine
    while (line != null) {
      read ++= line
      read ++= "\n"
      line = scala.Console.in.readLine
    }
    read.toString
  }

}
