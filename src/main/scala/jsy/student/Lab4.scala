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
      case h1 :: _ => if (h == h1) acc; else h :: acc;
    }
  }

  def mapFirst[A](l: List[A])(f: A => Option[A]): List[A] = l match {
    case Nil => l
    case h :: t => f(h) match {
      case None => h :: mapFirst(t)(f)
      case Some(a) => a :: t
    }
  }

  /* Trees */

  def foldLeft[A](t: Tree)(z: A)(f: (A, Int) => A): A = {
    def loop(acc: A, t: Tree): A = t match {
      case Empty => acc
      case Node(l, d, r) => loop(f(loop(acc, l), d), r)
    }
    loop(z, t)
  }

  def sum(t: Tree): Int = foldLeft(t)(0){ (acc, d) => acc + d }

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


  /*** Rename bound variables in e ***/

  def rename(e: Expr)(fresh: String => String): Expr = {
    def ren(env: Map[String,String], e: Expr): Expr = {
      e match {
        case N(_) | B(_) | Undefined | S(_) => e
        case Print(e1) => Print(ren(env, e1))

        case Unary(uop, e1) => Unary(uop, ren(env, e1))
        case Binary(bop, e1, e2) => Binary(bop, ren(env, e1), ren(env, e2))
        case If(e1, e2, e3) => If(ren(env, e1), ren(env, e2), ren(env, e3))
        case Var(y) => env.get(y) match {
          // case Some(x) => Var(env(x))
          case Some(x) => Var(x)
          case None => Var(y)
        }
        case Decl(mode, y, e1, e2) => {
          val yp = fresh(y)
          Decl(mode, yp, ren(env, e1), ren(env + (y -> yp), e2))
        }
        case Function(p, params, tann, e1) => {
          val (pp, envp): (Option[String], Map[String,String]) = p match {
            case None => (None, env)
            case Some(x) => {
              val fresh_var = fresh(x)
              (Some(fresh_var), env + (x -> fresh_var))
            }
          }
          val (paramsp, envpp) = params.foldRight( (Nil: List[(String,MTyp)], envp) ) {
            case ((pn, pt), (paramsAcc, envAcc)) => {
              val fresh_var = fresh(pn)
              ((fresh_var, pt) :: paramsAcc, envAcc + (pn -> fresh_var))
            }
          }
          Function(pp, paramsp, tann, ren(envpp, e1))
        }
        case Call(e1, args) => Call(ren(env, e1), args.map{arg => ren(env, arg)})
        // should obj fields be updated by renaming?
        // case Obj(fields) => Obj(fields.map{case (fKey, fValue) => (fKey, ren(env, fValue))})
        case Obj(fields) => Obj(fields.map{case (fKey, fValue) => (fresh(fKey), ren(env, fValue))})
        case GetField(e1, f) => GetField(ren(env, e1), fresh(f))
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
        case (_, tgot) => err(tgot, e2)
      }
      case Binary(Minus|Times|Div, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TNumber, TNumber) => TNumber
        case (tgot, _) => err(tgot, e1)
        case (_, tgot) => err(tgot, e2)
      }
      // what error to return.
      case Binary(Eq|Ne, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TFunction(_, _), _) => err(typeof(env, e1), e1)
        case (_, TFunction(_, _)) => err(typeof(env, e2), e2)
        case (t1, t2) => if (t1 == t2 && !hasFunctionTyp(t1)) TBool else err(t1, e1)
        case (tgot, _) => err(tgot, e1)
        case (_, tgot) => err(tgot, e2)
      }
      case Binary(Lt|Le|Gt|Ge, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TString, TString) => TBool
        case (TNumber, TNumber) => TBool
        case (tgot, _) => err(tgot, e1)
        case (_, tgot) => err(tgot, e2)
      }
      case Binary(And|Or, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TBool, TBool) => TBool
        case (tgot, _) => err(tgot, e1)
        case (_, tgot) => err(tgot, e2)
      }
      case Binary(Seq, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (t1, t2) => t1; t2
        case (tgot, _) => err(tgot, e1)
        case (_, tgot) => err(tgot, e2)
      }
      // what is the error type if the rule doesn't match?
      case If(e1, e2, e3) => typeof(env, e1) match {
        case TBool => {
          val e2_type = typeof(env, e2)
          val e3_type = typeof(env, e3)
          if (e2_type == e3_type) e2_type else err(e2_type, e2)
        }
        // case (_, _, tgot) => err(tgot, e3)
      }
      // mapValues
      case Obj(fields) => TObj(fields.map{case (k, ei) => (k, typeof(env, ei))})
      case GetField(e1, f) => typeof(env, e1) match {
        case TObj(fields) if fields.contains(f) => fields(f)
        case tgot => err(tgot, e1)
      }

      case Decl(_, x, e1, e2) => {
        val newEnv = env + (x -> typeof(env, e1))
        typeof(newEnv, e2)
      }

      case Function(p, params, tann, e1) => {
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (p, tann) match {
          case (None, _) => env
          case (Some(x), Some(y)) => env + (x -> TFunction(params, y))
          /***** Add cases here *****/
          case _ => err(TUndefined, e1)
        }
        // Bind to env2 an environment that extends env1 with bindings for params.
        val env2 = (params.foldLeft(env1){
          case (acc, (s, MTyp(_, t))) => acc + (s -> t)
        })
        //val env3 = env1 :: env2
        // Infer the type of the function body
        val t1 = typeof(env2, e1)
        // Check with the possibly annotated return type
        tann match {
          case None => TFunction(params, t1)
          case Some(x) => {
            if (x == t1) TFunction(params, x) else err(TFunction(params, x), e1)
          }
        }
      }
      case Call(e1, args) => typeof(env, e1) match {
        case TFunction(params, tret) if (params.length == args.length) =>
          (params zip args).foreach {
            //val argType =
            case ((_, MTyp(_, t)), arg) => {
              val arg_type = typeof(env, arg)
              if (arg_type != t) err(arg_type, arg)
              typeof(env, arg)
            }
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
      case Some(e2) => loop(e2, n+1)
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
      // base case.  var shadowing - x.  var y - this base case var. replace if equal.
      case Var(y) => if (x == y) esub else e
      case Decl(mode, y, e1, e2) => if (x == y) Decl(mode, x, subst(e1), e2) else Decl(mode, y, subst(e1), subst(e2))
        /***** Cases needing adapting from Lab 3 */
      case Function(p, params, tann, e1) => p match {
        /* DoCall */
        case None => if (params.contains(x)) e else Function(None, params, tann, subst(e1))
        /* DoCallRec */
        case Some(y) => {
          /* function remains the same if x is redeclared by function name or param */
          if (x == y || params.contains(x)) e
          /* otherwise recursively call substitute */
          // else Function(Some(y), params, tann, subst(e1)
          else Function(Some(y), params, tann, substitute(e1, esub, x))
        }
      }
      // recurses in now for each argument, since multi-argument.
      case Call(e1, args) => Call(subst(e1), args.map{arg => subst(arg)})
        /***** New cases for Lab 4 */
      // sub into each value in the object which may contain vars that need substitution
      case Obj(fields) => Obj(fields.map{ case (fkey, fval) => (fkey, subst(fval)) })
      // do substitutions for object used in get field. -- is this right?  or should be just be in obj declaration?
      // or do we sub first in get field.s
      case GetField(e1, f) =>if (x == f) e else GetField(subst(e1), f)
    }

    // 1. find free vars if they exist
    //    (we are given helper function).
    // 2. define 'fresh' which will update name itself (this is callback to rename)
    // 3. rename updates vars and env with 'fresh' var and mapping from (oldVar -> freshVar)
    // 4. curry rename with fresh.

    val fvs = freeVars(e)
    // of not contains.  we want to rename free variables.
    def fresh(x: String): String = if (fvs.contains(x)) fresh(x + "$") else x

    subst(rename(e)(fresh))
  }

  /* Check whether or not an expression is reducible given a mode. */
  def isRedex(mode: Mode, e: Expr): Boolean = mode match {
    // reduce if it's not yet reduced to be a value.
    case MConst => !isValue(e)
    // do not evaluate until necessary.  lazy eval
    case MName => false
  }

  /* A small-step transition. */
  def step(e: Expr): Expr = {
    require(!isValue(e), s"step: e ${e} to step is a value")
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined
        /***** Cases needing adapting from Lab 3. */
      case Unary(Neg, N(v1)) if isValue(N(v1)) => N(-1 * v1)
      case Unary(Not, B(v1)) if isValue(B(v1)) => B(!v1)

      case Binary(Plus, S(v1), S(v2)) if isValue(S(v1)) && isValue(S(v2)) => S(v1 + v2)
      case Binary(Plus, N(v1), N(v2)) if isValue(N(v1)) && isValue(N(v2)) => N(v1 + v2)

      case Binary(Minus, N(v1), N(v2)) if isValue(N(v1)) && isValue(N(v2)) => N(v1 - v2)
      case Binary(Times, N(v1), N(v2)) if isValue(N(v1)) && isValue(N(v2)) => N(v1 * v2)
      case Binary(Div, N(v1), N(v2)) if isValue(N(v1)) && isValue(N(v2)) => N(v1 / v2)

      case Binary(bop @ (Lt|Le|Gt|Ge), v1, v2) if isValue(v1) && isValue(v2) => B(inequalityVal(bop, v1, v2))

      case Binary(Eq, v1, v2) if isValue(v1) && isValue(v2) => B(v1 == v2)
      case Binary(Ne, v1, v2) if isValue(v1) && isValue(v2) => B(v1 != v2)

      // v1 cases start
      case Binary(And, B(v1), v2) if isValue(B(v1)) => if (v1) v2 else B(v1)
      case Binary(Or, B(v1), v2) if isValue(B(v1)) => if (v1) B(v1) else v2

      case If(B(v1), e2, e3) if isValue(B(v1)) => if (v1) e2 else e3
      case Decl(m, x, v1, e2) if isValue(v1) && isRedex(m, v1) => substitute(e2, v1, x)
        /***** More cases here */
      case Call(v1, args) if isValue(v1) =>
        v1 match {
          case Function(p, params, _, e1) => {
            // put arg and param in key/value pairs
            // (param, arg)
            // ((String,MTyp), Expr)
            val pazip = params zip args
            if (pazip.forall{case ((s, MTyp(m, t)), ei) => isRedex(m, ei)}) {
              // get new body by iteratively doing substs for params.
              val e1p = pazip.foldRight(e1) {
                case (((s,_), ei), accBody) => substitute(accBody, ei, s)
              }
              p match {
                case None => e1p
                // recursive sub for function name, the def of function into
                // new function body.
                case Some(x1) => substitute(e1p, e1, x1)
              }
            }
            else {
              val pazipp = mapFirst(pazip.toList) {
                case ((s, MTyp(m, t)), ei) => if (isRedex(m, ei)) Some((s, MTyp(m,t)), step(ei)) else None
              }
              Call(v1, pazipp.map{x=> x._2})
            }
          }
          case _ => throw StuckError(e)
        }

      //case Obj(fields) => ???
      case GetField(e1, f) if isValue(e1) => e1 match {
        case Obj(fields) => fields.get(f) match {
          case Some(x) => x
          case _ => throw StuckError(e)
        }
      }
        /***** New cases for Lab 4. */

      /* Inductive Cases: Search Rules */
      case Print(e1) => Print(step(e1))
        /***** Cases from Lab 3. */
      /* SearchUnary */
      case Unary(uop, e1) => Unary(uop, step(e1))
      /* SearchBinary2 */
      case Binary(bop, e1, e2) if isValue(e1) => Binary(bop, e1, step(e2))
      /* SearchBinary */
      case Binary(bop, e1, e2) => Binary(bop, step(e1), e2)
      /* SearchGetField */
      case GetField(e1, f) => GetField(step(e1), f)
      /* SearchObj */
      case Obj(fields) => fields.find{case (fkey, fval) => !isValue(fval)} match {
        case Some((k, vali)) =>  Obj(fields + (k -> step(vali)))
        case None => Obj(fields)
      }
      /* SearchCall */
      case Call(e1, e2) => Call(step(e1), e2)
      /* SearchIf */
      case If(e1, e2, e3) => If(step(e1), e2, e3)
      /* SearchConst */
      case Decl(m, x, e1, e2) => Decl(m, x, step(e1), e2)
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
