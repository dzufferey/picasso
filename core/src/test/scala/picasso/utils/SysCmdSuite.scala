package picasso.utils

import org.scalatest._

class SysCmdSuite extends FunSuite {
     
  test("echo test") {
    val echo = new String(SysCmd.execWithInputAndGetOutput(Array("echo", "-n", "test"), Nil, "").left.get)
    assert("test" == echo)
  }
  
  test("cat test") {
    val cat = new String(SysCmd.execWithInputAndGetOutput(Array("cat"), Nil, "test").left.get)
    assert("test" == cat)
  }

  test("try yo run some program that does not exists") {
    intercept[java.io.IOException] {
      SysCmd.execWithInputAndGetOutput(Array("???"), Nil, "")
    }
  }

}

