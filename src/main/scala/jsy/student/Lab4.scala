package jsy.student

import jsy.lab4.Lab4Like

object Lab4 extends jsy.util.JsyApplication with Lab4Like {
  import jsy.lab4.ast._
  import jsy.lab4.Parser
  
  /*
   * CSCI 3155: Lab 4
   * <Your Name>
   * 
   * Partner: <Your Partner's Name>
   * Collaborators: <Any Collaborators>
   */

  /*
   * Fill in the appropriate portions above by replacing things delimited
   * by '<'... '>'.
   * 
   * Replace the '???' expression with your code in each function.
   *
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   *
   * Your lab will not be graded if it does not compile.
   *
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert. Simply put in a
   * '???' as needed to get something that compiles without error. The '???'
   * is a Scala expression that throws the exception scala.NotImplementedError.
   */
  
  /*** Collections and Higher-Order Functions ***/
  
  /* Lists */
  
  def compressRec[A](l: List[A]): List[A] = l match {
    case Nil | _ :: Nil => Nil
    case h1 :: (t1 @ (h2 :: _)) => h1 :: compressRec(t1.dropWhile(_ == h1))
  }
  
  def compressFold[A](l: List[A]): List[A] = l.foldRight(Nil: List[A]){
    (h, acc) => acc match {
      case Nil => h :: Nil
      case h1 :: _ => {
        if (h == h1) {  acc; }
        else { h :: acc; }
      }
    }
  }
  
  def mapFirst[A](l: List[A])(f: A => Option[A]): List[A] = l match {
    case Nil => l
    case h :: t =>  f(h) match {
      case None => h :: mapFirst(t)(f)
      case Some(a) =>   a :: t
    }
  }
  
  /* Trees */

  // what is z?  just fold left down left side of tree?
  def foldLeft[A](t: Tree)(z: A)(f: (A, Int) => A): A = {
    def loop(acc: A, t: Tree): A = t match {
      case Empty => acc
      case Node(l, d, r) => loop(f(loop(acc, l), d), r)
    }
    loop(z, t)
  }

  // An example use of foldLeft
  def sum(t: Tree): Int = foldLeft(t)(0){ (acc, d) => acc + d }

  // Create a tree from a list. An example use of the
  // List.foldLeft method.
  def treeFromList(l: List[Int]): Tree =
    l.foldLeft(Empty: Tree){ (acc, i) => acc insert i }
  
  def strictlyOrdered(t: Tree): Boolean = {
    val (b, _) = foldLeft(t)((true, None: Option[Int])){
      (acc, i) => acc match {
        case (b1, None) =>  (b1, Some(i))
        case (b1, Some(a)) => if (a < i) (b1, Some(a)) else (false, Some(a))
      }
    }
    b
  }

  // free variable capture

  /*** Rename bound variables in e ***/

  def rename(e: Expr)(fresh: String => String): Expr = {
    def ren(env: Map[String,String], e: Expr): Expr = {
      e match {
        case N(_) | B(_) | Undefined | S(_) => e
        case Print(e1) => Print(ren(env, e1))

        case Unary(uop, e1) => ???
        case Binary(bop, e1, e2) => ???
        case If(e1, e2, e3) => ???

        case Var(y) => ???

        case Decl(mode, y, e1, e2) =>
          val yp = fresh(y)
          ???

        case Function(p, params, tann, e1) => {
          val (pp, envp): (Option[String], Map[String,String]) = p match {
            case None => ???
            case Some(x) => ???
          }
          val (paramsp, envpp) = params.foldRight( (Nil: List[(String,MTyp)], envp) ) {
            ???
          }
          ???
        }

        case Call(e1, args) => ???

        case Obj(fields) => ???
        case GetField(e1, f) => ???
      }
    }
    ren(empty, e)
  }

  /*** Type Inference ***/

  // While this helper function is completely given, this function is
  // worth studying to see how library methods are used.
  def hasFunctionTyp(t: Typ): Boolean = t match {
    case TFunction(_, _) => true
    case TObj(fields) if (fields exists { case (_, t) => hasFunctionTyp(t) }) => true
    case _ => false
  }
  
  def typeof(env: TEnv, e: Expr): Typ = {
    def err[T](tgot: Typ, e1: Expr): T = throw StaticTypeError(tgot, e1, e)

    e match {
      case Print(e1) => typeof(env, e1); TUndefined
      case N(_) => TNumber
      case B(_) => TBool
      case Undefined => TUndefined
      case S(_) => TString
      case Var(x) => lookup(env, x)
      case Unary(Neg, e1) => typeof(env, e1) match {
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }
      case Unary(Not, e1) => typeof(env, e1) match {
        case TBool => TBool
        case tgot => err(tgot, e1)
      }
      case Binary(Plus, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TString, TString) => TString
        case (TNumber, TNumber) => TNumber
        case (tgot, _) => err(tgot, e1)
        case (_, tgot) => err(tgot, e1)
      }
      case Binary(Minus|Times|Div, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TNumber, TNumber) => TNumber
        case (tgot, _) => err(tgot, e1)
        case (_, tgot) => err(tgot, e1)
      }
      case Binary(Eq|Ne, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TString, TString) => TBool
        case (TNumber, TNumber) => TBool
        case (tgot, _) => err(tgot, e1)
        case (_, tgot) => err(tgot, e1)
      }
      case Binary(Lt|Le|Gt|Ge, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TString, TString) => TBool
        case (TNumber, TNumber) => TBool
        case (tgot, _) => err(tgot, e1)
        case (_, tgot) => err(tgot, e1)
      }
      case Binary(And|Or, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TBool, TBool) => TBool
        case (tgot, _) => err(tgot, e1)
        case (_, tgot) => err(tgot, e1)
      }
      case Binary(Seq, e1, e2) =>
        ???
      case If(e1, e2, e3) => (typeof(env, e1), typeof(env, e2), typeof(env, e3)) match {
        //case (TBool, e2, e3) => typeof(env, e2) ==
      }
      case Obj(fields) => ???
      case GetField(e1, f) => ???

      case Decl(m, x, e1, e2) => ???

      case Function(p, params, tann, e1) => {
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (p, tann) match {
          /***** Add cases here *****/
          case _ => err(TUndefined, e1)
        }
        // Bind to env2 an environment that extends env1 with bindings for params.
        val env2 = ???
        // Infer the type of the function body
        val t1 = ???
        // Check with the possibly annotated return type
        ???
      }
      case Call(e1, args) => typeof(env, e1) match {
        case TFunction(params, tret) if (params.length == args.length) =>
          (params zip args).foreach {
            ???
          }
          tret
        case tgot => err(tgot, e1)
      }

    }
  }
  
  /*** Small-Step Interpreter ***/

  /*
   * Helper function that implements the semantics of inequality
   * operators Lt, Le, Gt, and Ge on values.
   *
   * We suggest a refactoring of code from Lab 2 to be able to
   * use this helper function in eval and step.
   *
   * This should the same code as from Lab 3.
   */
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1), s"inequalityVal: v1 ${v1} is not a value")
    require(isValue(v2), s"inequalityVal: v2 ${v2} is not a value")
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      /* DoInequalityString */
      case (S(v1), S(v2)) => bop match {
        case Gt => v1 > v2
        case Ge => v1 >= v2
        case Lt => v1 < v2
        case Le => v1 <= v2
      }
      /* DoInequalityNumber1 and DoInequalityNumber2 */
      case (N(v1), N(v2)) => bop match {
        case Gt => v1 > v2
        case Ge => v1 >= v2
        case Lt => v1 < v2
        case Le => v1 <= v2
      }
    }
  }

  /* This should be the same code as from Lab 3 */
  def iterate(e0: Expr)(next: (Expr, Int) => Option[Expr]): Expr = {
    def loop(e: Expr, n: Int): Expr = (next(e, n)) match {
      case None => e
      case Some(myFunctionName) => loop(myFunctionName, n+1)
    }
    loop(e0, 0)
  }

  /* Capture-avoiding substitution in e replacing variables x with esub. */
  def substitute(e: Expr, esub: Expr, x: String): Expr = {
    def subst(e: Expr): Expr = e match {
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(subst(e1))
        /***** Cases from Lab 3 */
      case Unary(uop, e1) => Unary(uop, subst(e1))
      case Binary(bop, e1, e2) => Binary(bop, subst(e1), subst(e2))
      case If(e1, e2, e3) => If(subst(e1), subst(e2), subst(e3))
      case Var(y) => if (x == y) esub else e
      case Decl(mode, y, e1, e2) => if (x == y) Decl(mode, x, subst(e1), e2) else Decl(mode, y, subst(e1), subst(e2))
        /***** Cases needing adapting from Lab 3 */
      case Function(p, params, tann, e1) =>
        ???
      case Call(e1, args) => ???
        /***** New cases for Lab 4 */
      case Obj(fields) => ???
      case GetField(e1, f) => ???
    }

    val fvs = freeVars(???)
    def fresh(x: String): String = if (???) fresh(x + "$") else x

    subst(e) // change this line when you implement capture-avoidance
  }

  /* Check whether or not an expression is reducible given a mode. */
  def isRedex(mode: Mode, e: Expr): Boolean = mode match {
    case MConst => ???
    case MName => ???
  }

  /* A small-step transition. */
  def step(e: Expr): Expr = {
    require(!isValue(e), s"step: e ${e} to step is a value")
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined
        /***** Cases needing adapting from Lab 3. */
      case Unary(Neg, v1) if isValue(v1) => ???
        /***** More cases here */
      case Call(v1, args) if isValue(v1) =>
        v1 match {
          case Function(p, params, _, e1) => {
            val pazip = params zip args
            if (???) {
              val e1p = pazip.foldRight(e1) {
                ???
              }
              p match {
                case None => ???
                case Some(x1) => ???
              }
            }
            else {
              val pazipp = mapFirst(pazip) {
                ???
              }
              ???
            }
          }
          case _ => throw StuckError(e)
        }
        /***** New cases for Lab 4. */

      /* Inductive Cases: Search Rules */
      case Print(e1) => Print(step(e1))
        /***** Cases from Lab 3. */
      case Unary(uop, e1) => ???
        /***** More cases here */
        /***** Cases needing adapting from Lab 3 */
      case Call(v1 @ Function(_, _, _, _), args) => ???
      case Call(e1, args) => ???
        /***** New cases for Lab 4. */

      /* Everything else is a stuck error. Should not happen if e is well-typed.
       *
       * Tip: you might want to first develop by comment out the following line to see which
       * cases you have missing. You then uncomment this line when you are sure all the cases
       * that you have left the ones that should be stuck.
       */
      case _ => throw StuckError(e)
    }
  }
  
  
  /* External Interfaces */
  
  //this.debug = true // uncomment this if you want to print debugging information
  this.maxSteps = Some(1000) // comment this out or set to None to not bound the number of steps.
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file
}
