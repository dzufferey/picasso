package picasso.utils

import org.scalatest._

class SysCmdSuite extends FunSuite {
     
  test("echo test") {
    val (code, echo, err) = SysCmd(Array("echo", "-n", "test"), "")
    assert("test\n" == echo, "code = " + code + ", output = " + echo + ", err = " + err)
  }
  
  test("cat test") {
    val (code, cat, err) = SysCmd(Array("cat"), "test")
    assert("test\n" == cat, "code = " + code + ", output = " + cat + ", err = " + err)
  }

  test("try yo run some program that does not exists") {
    intercept[java.io.IOException] {
      SysCmd(Array("???"))
    }
  }

}

