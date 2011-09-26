package pingpong

import scala.actors.Actor
import scala.actors.Actor._

abstract class PingMessage
case object Start extends PingMessage
case object Pong extends PingMessage

abstract class PongMessage
case object Ping extends PongMessage
case object Stop extends PongMessage

object Actor1 {

  def main(args: Array[String]) = {
    val pong = new Pong
    val ping = new Ping(100000, pong)
    ping.start
    pong.start
    ping ! Start
  }

}

class Ping(count: Int, pong: Actor) extends Actor {
  var sendPing : Boolean = false
  
  var pingsLeft = count
  
  def act() {
    println("Ping: Initializing with count "+count+": "+pong)
    //TODO problem with local variables and closures
    //var pingsLeft = count
    while(true) {
      if(sendPing) {
        pong ! Ping
        pingsLeft = pingsLeft - 1
        sendPing = false
      } else {
        if (pingsLeft <= 0) {
          println("Ping: Stop.")
          pong ! Stop
          exit('stop)
        } else {
          receive {
            case Start =>
              println("Ping: starting.")
              pong ! Ping
              pingsLeft = pingsLeft - 1
            case Pong =>
              if (pingsLeft % 1000 == 0)
                println("Ping: pong from: "+sender)
              sendPing = (pingsLeft > 0);
          }
        }
      }
    }
  }
}

class Pong extends Actor {

  var pongCount = 0

  def act() {
    //TODO problem with local variables and closures
    //var pongCount = 0
    loop {
      react {
        case Ping =>
          if (pongCount % 1000 == 0)
            println("Pong: ping "+pongCount+" from "+sender)
          sender ! Pong
          pongCount = pongCount + 1
        case Stop =>
          println("Pong: Stop.")
          exit('stop)
      }
    }
  }
}
