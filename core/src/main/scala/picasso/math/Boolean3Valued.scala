package picasso.math

object Boolean3Valued {

  type B3V = Int

  val True: B3V = 1
  val False: B3V = 0
  val Unkown: B3V = -1

  def and(a: B3V, b: B3V): B3V = a & b
  def or(a: B3V, b: B3V): B3V = a | b
  def xor(a: B3V, b: B3V): B3V = if ((a | b) == Unkown) Unkown else a ^ b

}
