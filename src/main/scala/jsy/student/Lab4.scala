package jsy.student

import jsy.lab4.Lab4Like

object Lab4 extends jsy.util.JsyApplication with Lab4Like {
  import jsy.lab4.ast._
  
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
    case Nil | _ :: Nil => l
    case h1 :: (t1 @ (h2 :: _)) =>
      if (h1 == h2) compressRec(t1) else h1 :: compressRec(t1)
  }
  
  def compressFold[A](l: List[A]): List[A] = l.foldRight(Nil: List[A]){
    (h, acc) => acc match {
      case Nil => h :: acc
      case (h1 :: _) => if (h == h1) acc else h :: acc
    }
  }
  
  def mapFirst[A](l: List[A])(f: A => Option[A]): List[A] = l match {
    case Nil => l
    case h :: t => f(h) match {
      case Some(h1) => h1 :: t
      case None => h :: mapFirst(t)(f)
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

  // An example use of foldLeft
  def sum(t: Tree): Int = foldLeft(t)(0){ (acc, d) => acc + d }

  // Create a tree from a list. An example use of the
  // List.foldLeft method.
  def treeFromList(l: List[Int]): Tree =
    l.foldLeft(Empty: Tree){ (acc, i) => acc insert i }

  def strictlyOrdered(t: Tree): Boolean = {
    val (b, _) = foldLeft(t)((true, None: Option[Int])){
      case ((flag, prev), d) => prev match {
        case Some(n) => (flag && (d > n), Some(d))
        case None => (flag, Some(d))
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
          case Some(yp) => Var(yp)
          case None => Var(y)
        }

        case Decl(mode, y, e1, e2) =>
          val yp = fresh(y)
          Decl(mode, yp, ren(env,e1), ren(env+(y->yp), e2))

        case Function(p, params, tann, e1) => {
          val (pp, envp): (Option[String], Map[String,String]) = p match {
            case None => (None, env)
            case Some(p) => {
              val fp = fresh(p)
              (Some(fp), env+(p->fp))
            }
          }
          val (paramsp, envpp) = params.foldRight( (Nil: List[(String,MTyp)], envp) ) {
            case ((p, typ), (pa, ea)) => {
              val fp = fresh(p)
              ((fp, typ)::pa, (ea+(p->fp)))
            }
          }
          Function(pp, paramsp, tann, ren(envpp, e1))
        }

        case Call(e1, args) => Call(ren(env, e1), args.map(ren(env, _)))

        case Obj(fields) => Obj(fields.mapValues(ren(env,_)))
        case GetField(e1, f) => GetField(ren(env,e1), f)
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

        /* TypeVar */
      case Var(x) => lookup(env, x)

        /* TypeNeg */
      case Unary(Neg, e1) => typeof(env, e1) match {
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }

        /* TypeNot */
      case Unary(Not, e1) => typeof(env, e1) match {
        case TBool => TBool
        case tgot => err(tgot, e1)
      }

        /* TypeSeq */
      case Binary(Seq, e1, e2) =>
        typeof(env, e1); typeof(env, e2)

        /* TypeArithPlus TypePlusString */
      case Binary(Plus, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TNumber, TNumber) => TNumber
        case (TString, TString) => TString
        case (TNumber | TString, tgot) => err(tgot, e2)
        case (tgot,_) => err(tgot, e1)
      }

        /* TypeArith */
      case Binary(Minus|Times|Div, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TNumber, TNumber) => TNumber
        case (TNumber, tgot) => err(tgot, e2)
        case (tgot, _) => err(tgot, e1)
      }

        /* TypeInequalityNumber TypeInequalityString */
      case Binary(Lt|Le|Gt|Ge, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TNumber, TNumber) => TBool
        case (TString, TString) => TBool
        case (TNumber | TString, tgot) => err(tgot, e2)
        case (tgot,_) => err(tgot, e1)
      }

        /* TypeEquality */
      case Binary(Eq|Ne, e1, e2) if (typeof(env, e1) == typeof(env, e2) && !hasFunctionTyp(typeof(env, e1))) => TBool

      case Binary(Eq|Ne, e1, e2) => err(typeof(env, e1), e1)

        /* TypeAndOr */
      case Binary(And|Or, e1, e2) => (typeof(env, e1), typeof(env, e2)) match {
        case (TBool, TBool) => TBool
        case (TBool, tgot) => err(tgot, e2)
        case (tgot, _) => err(tgot, e1)
      }

        /* TypeIf */
      case If(e1, e2, e3) => typeof(env,e1) match {
        case TBool => {
          if (typeof(env, e2) == typeof(env, e3)) typeof(env, e2)
          else err(typeof(env, e2), e2)
        }
        case _ => err(typeof(env, e1), e1)
      }

        /* TypeDecl */
      case Decl(m, x, e1, e2) => typeof(extend(env, x, typeof(env, e1)), e2)

        /* TypeCall */
      case Call(e1, args) => typeof(env, e1) match {
        case TFunction(params, tret) if (params.length == args.length) =>
          (params zip args).foreach {
            case ((_, MTyp(_,t)), arg) => if (t != typeof(env, arg)) err(t, arg)
          }
          tret
        case tgot => err(tgot, e1)
      }


        /* TypeObject */
      case Obj(fields) => TObj(fields.mapValues(typeof(env, _)))

        /* TypeGetField */
      case GetField(e1, f) => typeof(env, e1) match {
        case TObj(fields) => if (fields.contains(f)) fields(f) else err(typeof(env,e1),e1)
        case tgot => err(tgot, e1)
      }


      case Function(p, params, tann, e1) => {
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recursive.
        val env1 = (p, tann) match {
          /***** Add cases here *****/
          case (None, _) => env
          case (Some(f), Some(ann)) => extend(env, f, TFunction(params, ann))
          case (Some(f), None) => err(TUndefined, e1)
          case _ => err(TUndefined, e1)
        }
        // Bind to env2 an environment that extends env1 with bindings for params.
        val env2 = params.foldLeft(env1){
          case (acc, (s, MTyp(_,t))) => extend(acc,s,t)
        }

        // Infer the type of the function body
        val t1 = typeof(env2, e1)
        // Check with the possibly annotated return type
        tann match {
          case None => TFunction(params, t1)
          case Some(ann) => if (ann == t1) TFunction(params, ann) else err(TFunction(params, ann), e1)
        }
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
      case (S(s1), S(s2)) => bop match {
        case Ge => s1 >= s2
        case Gt => s1 > s2
        case Le => s1 <= s2
        case Lt => s1 < s2
        case _ => false
      }

      case (N(n1), N(n2)) => bop match {
        case Ge => n1 >= n2
        case Gt => n1 > n2
        case Le => n1 <= n2
        case Lt => n1 < n2
        case _ => false
      }

      case (_,_) => false
    }
  }

  /* This should be the same code as from Lab 3 */
  def iterate(e0: Expr)(next: (Expr, Int) => Option[Expr]): Expr = {
    def loop(e: Expr, n: Int): Expr = next(e, n) match {
      case None => e
      case Some(e1) => loop(e1, n+1)
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
      case Var(y) => if (x==y) esub else Var(y)
      case Decl(mode, y, e1, e2) => if (x==y) Decl(mode, y, subst(e1), e2) else Decl(mode, y, subst(e1), subst(e2))
        /***** Cases needing adapting from Lab 3 */
      case Function(p, params, tann, e1) =>  {
        params.find(_._1 == x) match {
          case Some(_) => Function(p, params, tann, e1)
          case None => {
            if (x == p) Function(p, params, tann, e1)
            else Function(p, params, tann, subst(e1))
          }
        }
      }
      case Call(e1, args) => Call(subst(e1), args.map(subst(_)))
        /***** New cases for Lab 4 */
      case Obj(fields) => Obj(fields.mapValues(f => subst(f)))
      case GetField(e1, f) => GetField(substitute(e1, esub, x), f)
    }

    val fvs = freeVars(esub)
    def fresh(x: String): String = if (fvs.contains(x)) fresh(x + "$") else x
    subst(rename(e)(fresh))
  }
  /* Check whether or not an expression is reducible given a mode. */
  def isRedex(mode: Mode, e: Expr): Boolean = mode match {
    case MConst => !isValue(e)
    case MName => false
  }

  /* A small-step transition. */
  def step(e: Expr): Expr = {
    require(!isValue(e), s"step: e ${e} to step is a value")
    e match {
      /* Base Cases: Do Rules */

        /* DoPrint */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined
        /***** Cases needing adapting from Lab 3. */

        /* DoNeg */
      case Unary(Neg, N(v1)) if isValue(N(v1)) => N(-v1)
        /* DoNot */
      case Unary(Not, B(v1)) if isValue(B(v1)) => B(!v1)
        /* DoSeq */
      case Binary(Seq, v1, e2) if isValue(v1) => e2

        /* DoArith */
      case Binary(Plus, N(n1), N(n2)) => N(n1 + n2)
      case Binary(Minus, N(n1), N(n2)) => N(n1 - n2)
      case Binary(Times, N(n1), N(n2)) => N(n1 * n2)
      case Binary(Div, N(n1), N(n2)) => N(n1 / n2)
        /* DoPlusString */
      case Binary(Plus, S(s1), S(s2)) => S(s1 + s2)

        /* DoInequalityNumber */
      case Binary(bop @(Ge | Gt | Le | Lt), N(n1), N(n2)) => B(inequalityVal(bop, N(n1), N(n2)))

        /* DoInequalityString */
      case Binary(bop @(Ge | Gt | Le | Lt), S(s1), S(s2)) => B(inequalityVal(bop, S(s1), S(s2)))

        /* DeEquality */
      case Binary(Eq, v1, v2) if isValue(v1) && isValue(v2) => B(v1 == v2)
      case Binary(Ne, v1, v2) if isValue(v1) && isValue(v2) => B(v1 != v2)

        /* DoAndTrue DoAndFalse */
      case Binary(And, B(b1), e2) => if (b1) e2 else B(b1)
        /* DoOrTrue DoOrFalse */
      case Binary(Or, B(b1), e2) => if (b1) B(b1) else e2

        /* DoIfTrue DoIfFalse */
      case If(B(b1), e2, e3) => if (b1) e2 else e3

        /* DoDecl */
      case Decl(m, x, e1, e2) if !isRedex(m, e1) => substitute(e2, e1, x)

        /***** More cases here */

        /* DoCall */
      case Call(v1, args) if isValue(v1) =>
        v1 match {
          case Function(p, params, _, e1) => {
            val pazip = params zip args
            if (pazip.forall{ case ((_, MTyp(m, _)), arg) => !isRedex(m, arg)}) {
              val e1p = pazip.foldRight(e1) {
                case (((p, _), arg), accexpr) => substitute(accexpr, arg, p)
              }

              /* DoCallRec */
              p match {
                case None => e1p
                case Some(x1) => substitute(e1p, v1, x1)
              }
            }

              /* SearchCall2 */
            else {
              val pazipp = mapFirst(pazip) {
                case ((p, MTyp(m, t)), e) => if (isRedex(m, e)) Some((p, MTyp(m, t)), step(e)) else None
              }
              Call(v1, pazipp.unzip._2)
            }
          }
          case _ => throw StuckError(e)
        }
        /***** New cases for Lab 4. */

        /* DoGetField */
      case GetField(e1, x) if (isValue(e1)) => e1 match {
        case Obj(fields) if (fields.contains(x)) => fields(x)
        case _ => throw StuckError(e)
      }
      /* Inductive Cases: Search Rules */

        /* SearchPrint */
      case Print(e1) => Print(step(e1))
        /***** Cases from Lab 3. */

        /* Search Unary */
      case Unary(uop, e1) => Unary(uop, step(e1))

        /* SearchBinary1 */
      case Binary(bop, e1, e2) if !isValue(e1) => Binary(bop, step(e1), e2)
        /* SearchBinary2 */
      case Binary(bop, v1, e2) if !isValue(e2) => Binary(bop, v1, step(e2))
        /* SearchIf */
      case If(e1, e2, e3) if !isValue(e1) => If(step(e1), e2, e3)
        /***** More cases here */
        /***** Cases needing adapting from Lab 3 */
        /* SearchDecl */
      case Decl(m, x, e1, e2) if isRedex(m, e1) => Decl(m, x, step(e1), e2)

        /* SearchCall1 */
      case Call(e1, args) if !isValue(e1) => Call(step(e1), args)


        /***** New cases for Lab 4. */

        /* SearchObject */
      case Obj(fields) => fields.find(f => !isValue(f._2)) match {
          case Some((f, exp)) => Obj(fields+ (f -> step(exp)))
          case None => Obj(fields) // impossible
      }

        /* SearchGetField */
      case GetField(e1, x) => GetField(step(e1), x)

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
  
  this.debug = true // uncomment this if you want to print debugging information
  this.maxSteps = Some(1000) // comment this out or set to None to not bound the number of steps.
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file
}
