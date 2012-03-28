package picasso.model.integer
  
import scala.collection.GenSeq

  //what is an ARMC/T2/integer program:
  // program location
  // variables
  // transition (var updates for T2, set of constraints for ARMC)
  // a start location
  // cutpoints (for ARMC)
  //the simplest thing might be to have somthing between T2 and ARMC:
  // get updates like T2, but with an all at the same time semantics like ARMC.
  // we want automatic frame generation -> havoc statement.

/** Integer Program.
 *  Integer program are use during the termination proof of DBP.
 *  Right now their purpose is just these termination check (not safety).
 */
class Program(init: State, trs: GenSeq[Transition]) extends picasso.math.TransitionSystem {
  
  type S = State
  
  //transition type
  type T = Transition

  def transitions: GenSeq[T] = trs


  def printForARMC = {
    sys.error("TODO")
  }
  
  def printForT2 = {
    sys.error("TODO")
  }
}
