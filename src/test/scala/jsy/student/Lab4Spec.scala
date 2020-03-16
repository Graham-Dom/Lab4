package jsy.student

import jsy.lab4.Lab4Like
import jsy.lab4.Parser.parse
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

  /***** Interpreter Tests *****/

  {
    val xtype = TNumber
    val tenvx = extend(empty, "x", xtype)


    "TypeVar" should "perform TypeVar" in {
      assertResult(xtype) {
        typeof(tenvx, Var("x"))
      }
    }

    "TypeNeg" should "be a number" in {
      assertResult(TNumber) {
        typeof(empty, Unary(Neg, N(4)))
      }
    }

    it should "throw an error" in {
      assertThrows[StaticTypeError]{
        typeof(empty, Unary(Neg, S("hi")))
      }
    }

    "TypeArith" should "be a number" in {
      assertResult(TNumber) {
        typeof(empty, Binary(Plus, N(3), N(4)))
      }
      assertResult(TNumber) {
        typeof(empty, Binary(Minus, N(3), N(4)))
      }
      assertResult(TNumber) {
        typeof(empty, Binary(Times, N(3), N(4)))
      }
      assertResult(TNumber) {
        typeof(empty, Binary(Div, N(3), N(4)))
      }
      assertResult(TNumber) {
        typeof(empty, Binary(Minus, Binary(Plus, N(3), N(4)), N(2)))
      }
    }

    it should "throw an error" in{
      assertThrows[StaticTypeError]{
        typeof(empty,Binary(Div, N(3), S("hi")))
      }
      assertThrows[StaticTypeError]{
        typeof(empty,Binary(Minus, N(3), S("hi")))
      }
      assertThrows[StaticTypeError]{
        typeof(empty,Binary(Times, S("hi"), N(4)))
      }
      assertThrows[StaticTypeError]{
        typeof(empty,Binary(Plus, N(3), B(true)))
      }
    }

    "TypePlusString" should "be a string" in {
      assertResult(TString) {
        typeof(empty, Binary(Plus, S("hi"), S("hi")))
      }
    }

    it should "throw an error" in {
      assertThrows[StaticTypeError]{
        typeof(empty,Binary(Plus, S("hi"), B(true)))
      }

      assertThrows[StaticTypeError]{
        typeof(empty,Binary(Plus, S("hi"), N(3)))
      }
    }

    "TypeInequalityNumber" should "be a bool" in {
      assertResult(TBool) {
        typeof(empty, Binary(Gt, N(3), N(4)))
      }
      assertResult(TBool) {
        typeof(empty, Binary(Lt, N(3), N(4)))
      }
      assertResult(TBool) {
        typeof(empty, Binary(Le, N(3), N(4)))
      }
      assertResult(TBool) {
        typeof(empty, Binary(Lt, N(3), N(4)))
      }
    }

    it should "throw an error" in {
      assertThrows[StaticTypeError]{
        typeof(empty,Binary(Ge, N(3), S("hi")))
      }
      assertThrows[StaticTypeError]{
        typeof(empty,Binary(Lt, N(3), S("hi")))
      }
      assertThrows[StaticTypeError]{
        typeof(empty,Binary(Gt, S("hi"), N(4)))
      }
      assertThrows[StaticTypeError]{
        typeof(empty,Binary(Le, N(3), B(true)))
      }
    }

    "TypeInequalityString" should "be a bool" in {
      assertResult(TBool) {
        typeof(empty, Binary(Gt, S("hi"), S("Yo")))
      }
      assertResult(TBool) {
        typeof(empty, Binary(Ge, S("hi"), S("Yo")))
      }
      assertResult(TBool) {
        typeof(empty, Binary(Lt, S("hi"), S("Yo")))
      }
      assertResult(TBool) {
        typeof(empty, Binary(Le, S("hi"), S("Yo")))
      }
    }

    "TypeEquality" should "return bool if things have the same type" in {
      assertResult(TBool){
        typeof(empty, Binary(Eq, N(1), N(2)))
      }
      assertResult(TBool){
        typeof(empty, Binary(Eq, B(true), B(false)))
      }
      assertResult(TBool){
        typeof(empty, Binary(Eq, S("hi"), S("yo")))
      }
      assertResult(TBool){
        typeof(empty, Binary(Eq, Undefined, Undefined))
      }
      assertResult(TBool){
        typeof(empty, Binary(Ne, N(1), N(2)))
      }
      assertResult(TBool){
        typeof(empty, Binary(Ne, B(true), B(false)))
      }
      assertResult(TBool){
        typeof(empty, Binary(Ne, S("hi"), S("yo")))
      }
      assertResult(TBool){
        typeof(empty, Binary(Ne, Undefined, Undefined))
      }
    }

    it should "throw otherwise" in {
      assertThrows[StaticTypeError]{
        typeof(empty, Binary(Eq, N(1), S("2")))
      }
      assertThrows[StaticTypeError]{
        typeof(empty, Binary(Eq, B(true), S("2")))
      }
      assertThrows[StaticTypeError]{
        typeof(empty, Binary(Eq, S("undefined"), Undefined))
      }
      assertThrows[StaticTypeError]{
        typeof(empty, Binary(Ne, N(1), S("2")))
      }
      assertThrows[StaticTypeError]{
        typeof(empty, Binary(Ne, B(true), S("2")))
      }
      assertThrows[StaticTypeError]{
        typeof(empty, Binary(Ne, S("undefined"), Undefined))
      }
    }

    "TypeAndOr" should "take two bools" in {
      assertResult(TBool){
        typeof(empty,Binary(And, B(true), B(false)))
      }
      assertResult(TBool){
        typeof(empty,Binary(And, B(false), B(false)))
      }
      assertResult(TBool){
        typeof(empty,Binary(Or, B(true), B(false)))
      }
      assertResult(TBool){
        typeof(empty,Binary(Or, B(false), B(false)))
      }
    }

    it should "throw otherwise" in {
      assertThrows[StaticTypeError]{
        typeof(empty, Binary(And, B(true), S("hello")))
      }
      assertThrows[StaticTypeError]{
        typeof(empty, Binary(And, B(true), N(1)))
      }
      assertThrows[StaticTypeError]{
        typeof(empty, Binary(And, N(2), B(false)))
      }
    }

    "TypeIf" should "Only allow bool for e1" in {
      assertResult(TBool){
        typeof(empty, If(B(true), B(true), B(false)))
      }
      assertThrows[StaticTypeError]{
        typeof(empty, If(N(1), B(true), B(false)))
      }
      assertThrows[StaticTypeError]{
        typeof(empty, If(S("HI"), B(true), B(false)))
      }
      assertThrows[StaticTypeError]{
        typeof(empty, If(Undefined, B(true), B(false)))
      }
    }

    it should "Enforce the same type of e2 and e3" in {
      assertResult(TString){
        typeof(empty, If(B(true), S("hi"), S("bye")))
      }
      assertResult(TNumber){
        typeof(empty, If(B(true), N(2), N(3)))
      }
      assertResult(TUndefined){
        typeof(empty, If(B(true), Undefined, Undefined))
      }
      assertThrows[StaticTypeError]{
        typeof(empty, If(B(true), B(true), N(2)))
      }
      assertThrows[StaticTypeError]{
        typeof(empty, If(B(true), S("hi"), N(2)))
      }
    }

    "TypeDecl" should "return the type given the environment" in {
      assertResult(TNumber){
        typeof(empty, Decl(MConst, "x", N(30), Var("x")))
      }
      assertResult(TBool){
        typeof(empty, Decl(MConst, "x", B(true), Binary(And,Var("x"), Var("x"))))
      }
    }

    "TypeFunction" should "perform Typefunc" in {
      assertResult(TFunction(List(("x", MTyp(MConst, TNumber)), ("y", MTyp(MConst, TNumber))), TNumber)) {
        typeof(empty, parse("function fst(x: number, y: number): number { return x }"))
      }
      assertResult(TFunction(List(("x", MTyp(MConst, TBool)), ("y", MTyp(MConst, TNumber))), TBool)) {
        typeof(empty, parse("function fst(x: bool, y: number): bool { return x }"))
      }

      assertResult(TFunction(List(("x", MTyp(MConst, TNumber))), TNumber)) {
        typeof(empty, parse("function (x: number) { return x }"))
      }
    }

    "TypeCall" should "perform typecall" in {
      assertResult(TNumber) {
        typeof(empty, Call(parse("function fst(x: number, y: number): number { return x }"),List(N(1), N(2))))
      }
    }

    "TypeObject" should "perform typeobject" in {
      val obj = Obj(Map("a" -> N(3), "b" -> B(true), "c" -> S("hi"), "u" -> Undefined))
      assertResult(TObj(Map("a" -> TNumber, "b" -> TBool, "c" -> TString, "u" -> TUndefined))){
        typeof(empty, obj)
      }
    }

    it should "support nesting" in {
      val obj = Obj(Map("a" -> N(3), "o" -> Obj(Map("a" -> B(false)))))
      assertResult(TObj(Map("a" -> TNumber, "o" -> TObj(Map("a" -> TBool))))){
        typeof(empty, obj)
      }
    }

    "TypeGetField" should "do its job" in {
      val obj = Obj(Map("a" -> N(3), "b" -> B(true), "c" -> S("hi"), "u" -> Undefined))
      assertResult(TUndefined){
        typeof(empty, GetField(obj, "u"))
      }
    }

    it should "also support nesting" in {
      val obj = Obj(Map("a" -> N(3), "o" -> Obj(Map("a" -> B(false)))))
      assertResult(TBool){
        typeof(empty, GetField(GetField(obj, "o"), "a"))
      }
    }

    // Probably want to write some more tests for typeInfer, substitute, and step.

  }

  "Step Obj" should "step an expression field" in {
    assertResult(Obj(Map(("x" -> N(2)), "y" -> N(-3)))) {
      step(Obj(Map(("x" -> N(2)), "y" -> Unary(Neg, N(3)))))
    }
  }

  "substitute" should "work right" in {
    assertResult(Binary(Plus, N(3), N(3))){
      substitute(Binary(Plus, Var("x"), N(3)), N(3), "x")
    }
    assertResult(Decl(MName, "a", N(1), Binary(Plus,Var("a"), Var("b")))){
      substitute(Decl(MName, "a", N(1), Binary(Plus, Var("a"), Var("b"))),N(2),"a")
    }
  }

  it should "rename bound variables" in {
    assertResult(Decl(MName, "a$", N(1), Binary(Plus,Var("a$"), Binary(Plus, Var("a"), N(2))))){
      substitute(Decl(MName, "a", N(1), Binary(Plus, Var("a"), Var("b"))),Binary(Plus, Var("a"), N(2)),"b")
    }
  }

  "substitute function" should "substitute values into the function expression" in {
    val e = Binary(Plus, Var("x"), N(1))
    val f = Function(None, List(), None, e)
    assertResult(Function(None, List(), None, Binary(Plus, N(2), N(1)))){
      substitute(f, N(2), "x")
    }
  }

  it should "substitute expressions into the function expression" in {
    val e = Binary(Plus, Var("x"), N(1))
    val f = Function(None, List(), None, e)
    assertResult(Function(None, List(), None, Binary(Plus, Binary(Plus, N(3), N(2)), N(1)))){
      substitute(f, Binary(Plus, N(3), N(2)), "x")
    }
  }

  it should "preserve static scoping" in {
    val e = Binary(Plus, Var("x"), N(1))
    val f = Function(None, List(("x", MTyp(MName, TNumber))), None, e)
    assertResult(Function(None, List(("x", MTyp(MName, TNumber))), None, Binary(Plus, Var("x"), N(1)))){
      substitute(f, Binary(Plus, N(3), N(2)), "x")
    }
  }

  it should "rename commonly named variables from external substitution" in {
    val e = Binary(Plus, Var("a"), Var("b"))
    val f = Function(None, List(("a", MTyp(MName, TNumber))), None, e)
    assertResult(Function(None, List(("a$", MTyp(MName, TNumber))), None, Binary(Plus, Var("a$"), Var("a")))){
      substitute(f, Var("a"), "b")
    }
  }

  it should "rename the function name if it needs to" in {
    val e = Binary(Plus, Var("a"), N(1))
    val f = Function(Some("f"), List(), None, e)
    assertResult(Function(Some("f$"), List(), None, Binary(Plus, Var("f"), N(1)))){
      substitute(f, Var("f"), "a")
    }
  }

  "Substitute Call" should "perform substitution in the function and the args" in {
    val e = Binary(Plus, Var("a"), N(1))
    val f = Function(None, List(), None, e)
    assertResult(Call(Function(None, List(), None, Binary(Plus, N(2), N(1))), List(N(2)))){
      substitute(Call(f, List(Var("a"))), N(2), "a")
    }
  }

  "Call" should "substitute variable bindings" in {
    val e = Binary(Plus, Var("a"), Var("b"))
    val f = Function(None, List(("a", MTyp(MName, TNumber)), ("b", MTyp(MName, TNumber))), None, e)
    assertResult(Binary(Plus, N(1), N(2))){
      step(Call(f, List(N(1), N(2))))
    }
  }

  it should "reduce call by value params" in {
    val e = Binary(Plus, Var("a"), Var("b"))
    val f = Function(None, List(("a", MTyp(MConst, TNumber)), ("b", MTyp(MName, TNumber))), None, e)
    assertResult(Call(Function(None,List(("a",MTyp(MConst,TNumber)), ("b",MTyp(MName,TNumber))),None,Binary(Plus,Var("a"),Var("b"))),List(N(1.0), N(2.0)))){
      step(Call(f, List(Binary(Minus, N(2), N(1)), N(2))))
    }
  }

  it should "not reduce call by name params" in {
    val e = Binary(Plus, Var("a"), Var("b"))
    val f = Function(None, List(("a", MTyp(MName, TNumber)), ("b", MTyp(MName, TNumber))), None, e)
    assertResult(Binary(Plus, Binary(Minus, N(2), N(1)), N(2))){
      step(Call(f, List(Binary(Minus, N(2), N(1)), N(2))))
    }
  }

  "DoNeg" should "work" in {
    assertResult(N(-2)){
      step(Unary(Neg, N(2)))
    }
  }

  "DoIf" should "work" in {
    val e = If(Binary(And, B(true), B(false)), Binary(Plus, N(1), N(2)), Binary(Minus, N(3), N(4)))

    val e1 = step(e)
    assert(e1 == (If(B(false), Binary(Plus, N(1), N(2)), Binary(Minus, N(3), N(4)))))

    val e2 = step(e1)
    assert(e2 == (Binary(Minus, N(3), N(4))))

    val e3 = step(e2)
    assert(e3 == N(-1))
  }

  "DoDecl" should "Do const eval" in {
    val e = Decl(MConst, "x", Binary(Plus, N(3), N(2)), Binary(Div, Var("x"), N(5)))

    val e1 = step(e)
    assert(e1 == Decl(MConst, "x", N(5), Binary(Div, Var("x"), N(5))))

    val e2 = step(e1)
    assert(e2 == Binary(Div, N(5), N(5)))

    val e3 = step(e2)
    assert(e3 == N(1))
  }

  "DoDecl" should "Do lazy eval" in {
    val e = Decl(MName, "x", Binary(Plus, N(3), N(2)), Binary(Div, Var("x"), N(5)))

    val e1 = step(e)
    assert(e1 == Binary(Div, Binary(Plus, N(3), N(2)), N(5)))

    val e2 = step(e1)
    assert(e2 == Binary(Div, N(5), N(5)))

    val e3 = step(e2)
    assert(e3 == N(1))
  }

  "DoGetField" should "work" in {
    val obj = Obj(Map("a" -> Binary(Plus, N(1), N(1)), "b" -> Undefined, "o" -> Obj(Map("a" -> N(3)))))
    val e = GetField(obj, "b")
    val e1 = step(e)
    assert(e1 == GetField(Obj(Map("a" -> N(2), "b" -> Undefined, "o" -> Obj(Map("a" -> N(3))))), "b"))
    assert(step(e1) == Undefined)

    val e2 = GetField(GetField(obj, "o"), "a")
    val e3 = step(e2)

    assert(e3 == GetField(GetField(Obj(Map("a" -> N(2), "b" -> Undefined, "o" -> Obj(Map("a" -> N(3))))), "o"), "a"))

    val e4 = step(e3)
    assert(e4 == GetField(Obj(Map("a" -> N(3))), "a"))

    val e5 = step(e4)
    assert(e5 == N(3))
  }


  "the whole thing" should "work" in {
    val params = List(("x",MTyp(MConst,TNumber)), ("y",MTyp(MConst,TBool)))
    val args = List(N(4.0), B(true))
    val body = If(Var("y"),Binary(Plus,Var("x"),N(1.0)),Binary(Minus,Var("x"),N(1.0)))
    val f = Function(None,params,None,body)

    val e = Call(f, args)
    assert(typeof(empty, e) == TNumber)
    assert(iterateStep(e) == N(5))
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