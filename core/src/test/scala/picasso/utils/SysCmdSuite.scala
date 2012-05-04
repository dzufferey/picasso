package picasso.utils

import org.scalatest._

class SysCmdSuite extends FunSuite {
     
  test("echo test") {
    val (code, echo, err) = SysCmd(Array("echo", "-n", "test"), "")
    assert("test" == echo)
  }
  
  test("cat test") {
    val (code, cat, err) = SysCmd(Array("cat"), "test")
    assert("test" == cat)
  }

  test("try yo run some program that does not exists") {
    intercept[java.io.IOException] {
      SysCmd(Array("???"))
    }
  }

}

