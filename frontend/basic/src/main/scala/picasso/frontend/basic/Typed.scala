package picasso.frontend.basic

import picasso.math.hol.{Type, Wildcard => WildcardT}

trait Typed {
  
  //TODO type should be a val but no known at object creation, i.e. set only once

  var tpe: Type = WildcardT

  def setType(t: Type): this.type = {
    tpe = t
    this
  }

}
