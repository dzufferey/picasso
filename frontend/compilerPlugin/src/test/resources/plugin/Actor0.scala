
import scala.actors._
import scala.actors.Actor._

case object Start 
case object Stop 

object Actor0 extends Channel[Any] {

  def main(args: Array[String]) = {
    val pong = new Pong
    val ping = new Ping(pong)
    ping.start
    pong.start
    ping.send(Start, this)
    val done = ?
    ()
  }

}

class Ping(pong: Actor) extends Actor {
  
  def act() {
    loop {
      react {
        case Start =>
          pong ! Stop
          sender ! Stop
          exit('stop)
      }
    }
  }
}

class Pong extends Actor {

  def act() {
    loop {
      react {
        case Stop =>
          exit('stop)
      }
    }
  }
}
