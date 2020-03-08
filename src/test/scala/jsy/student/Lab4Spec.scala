package jsy.student

import jsy.lab4.Lab4Like
import jsy.lab4.ast._
import jsy.tester.JavascriptyTester
import org.scalatest._

class Lab4Spec(lab4: Lab4Like) extends FlatSpec {
  import lab4._

  /***** Higher-Function Exercises Tests *****/

  "compressRec/compressFold" should "compress List(1, 2, 2, 3, 3, 3)" in {
    val l1 = List(1, 2, 2, 3, 3, 3)
    val gold1 = List(1, 2, 3)
    assertResult(gold1) { compressRec(l1) }
    assertResult(gold1) { compressFold(l1) }
  } 
  
  "mapFirst" should "map the first element where f returns Some" in {
     val l1 = List(1, 2, -3, 4, -5)
     val gold1 = List(1, 2, 3, 4, -5)
     assertResult(gold1) {
       mapFirst(l1) { (i: Int) => if (i < 0) Some(-i) else None }
     }
  }
  
  "foldLeft" should "enable implementing treeFromList and sum" in {
    assertResult(6){
      sum(treeFromList(List(1, 2, 3)))
    }
  }

  "strictlyOrdered" should "check strict ordering of a binary search tree" in {
    assert(!strictlyOrdered(treeFromList(List(1,1,2))))
    assert(strictlyOrdered(treeFromList(List(1,2))))
  }

  "type test" should "return the right type" in {
    val res_type = TNumber
    val x = "x"
    val start_type = empty + (x -> TNumber)
    val start_expr = N(4.5)
    assertResult(res_type) {
      typeof(start_type, start_expr)
    }
  }

  it should "return the a number from an object" in {
    val res_type = TNumber
    val f = "f"
    val start_type = empty + (f -> TNumber)
    val start_expr = GetField(Obj(Map(f -> N(3.0))),f)
    assertResult(res_type) {
      typeof(start_type, start_expr)
    }
    GetField(Obj(Map(f -> N(3.0))),f)
  }

  it should "step to the return val of an obj" in {
    val f = "f"
    assertResult(N(3.0)) {
      step(GetField(Obj(Map(f -> N(3.0))),f))
    }
  }

  /***** Interpreter Tests *****/

  {
    val xtype = TNumber
    val tenvx = extend(empty, "x", xtype)

    "TypeVar" should "perform TypeVar" in {
      assertResult(xtype) {
        typeof(tenvx, Var("x"))
      }
    }

    // Probably want to write some more tests for typeInfer, substitute, and step.

  }

}

// An adapter class to pass in your Lab4 object.
class Lab4SpecRunner extends Lab4Spec(jsy.student.Lab4)

// The next bit of code runs a test for each .jsy file in src/test/resources/lab4.
// The test expects a corresponding .ans file with the expected result.
class Lab4JsyTests extends JavascriptyTester(None, "lab4", jsy.student.Lab4)

class Lab4Suite extends Suites(
  new Lab4SpecRunner,
  new Lab4JsyTests
)