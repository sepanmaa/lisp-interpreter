package lisp.interpreter
import scala.util.parsing.combinator._
import scalaz._
import Scalaz._
import scala.collection.mutable.Map


sealed trait LispValue
case class LispIdentifier(id: String) extends LispValue {
  override def toString = id.toString
}
case class LispNumber(val num: Int) extends LispValue {
  override def toString = num.toString
}
case class LispList(list: List[LispValue]) extends LispValue {
  override def toString = list match {
    case x :: xs => {
      "(" + xs.fold(x.toString)((acc, x) => acc + " " + x.toString) + ")"
    }
    case Nil => "()"
  }
}
case class LispDottedList(val list: List[LispValue], tail: LispValue) extends LispValue {
  override def toString = list match {
    case x :: xs => {
      "(" + xs.fold(x.toString)((acc, x) => acc + " " + x.toString) + " . " + tail.toString + ")"
    }
    case Nil => "()"
  }
}
case class LispString(str: String) extends LispValue {
  override def toString = "\"" + str + "\""
}
case class LispBool(b: Boolean) extends LispValue {
  override def toString = if (b) "#t" else "#f"
}
case class LispOp(fun: List[LispValue] => Validation[String, LispValue]) extends LispValue {
  override def toString = "<operator>"
}

case class LispProcedure(formals: List[String], body: List[LispValue], env: List[Map[String, LispValue]])
    extends LispValue {
  override def toString = "<procedure>"
}


class LispParser extends RegexParsers {
  override val skipWhitespace = false;

  def initial = """[a-z]""".r | """[\!\$\%\&\*\/\:\<\=\>\?\^\_]""".r

  def subseq = initial | """[0-9]""".r | "+" | "-" | "." | "@"

  def normalId = initial ~ rep(subseq) ^^ {
    case i ~ xs => LispIdentifier(i + xs.fold("")(_ + _))
  }

  def peculiarId = """(\+|\-|\.\.\.)""".r ^^ {
    case op => LispIdentifier(op)
  }

  def ident: Parser[LispValue] = normalId | peculiarId

  def string: Parser[LispValue] = """\"""".r ~> """[a-zA-Z]*""".r <~ """\"""".r ^^ {
    s => LispString(s)
  }

  def number: Parser[LispValue] = """[0-9]+""".r ^^ {
    case n => LispNumber(n.toInt)
  }

  def bool: Parser[LispValue] = ("#t" | "#f") ^^ {
    case "#t" => LispBool(true)
    case "#f" => LispBool(false)
  }

  def datum: Parser[LispValue] = ident | number | string | bool | list | quoted

  def quoted: Parser[LispValue] = """\'""".r ~> datum ^^ {
    x => LispList(List(LispIdentifier("quote"), x))
  }

  def list: Parser[LispValue] = normalList | dottedList

  def dottedList: Parser[LispValue] = {
    "(" ~> repsep(datum, """\s+""".r) ~ """\s+\.\s+""".r ~ datum <~ """\s*\)""".r ^^ {
      case xs ~ dot ~ x => LispDottedList(xs, x)
    }
  }

  def normalList: Parser[LispValue] = "(" ~> repsep(datum, """\s+""".r) <~ """\s*\)""".r ^^ {
    case xs => LispList(xs)
  }

  def read(input: String): ParseResult[LispValue] = {
    this.parseAll(datum, input)
  }
}


class Evaluator {
  def numOp(xs: List[LispValue], func: List[Int] => LispValue): Validation[String, LispValue] = {
    xs.map(toNumber).sequenceU :-> func
  }
  def boolOp(xs: List[LispValue], func: List[Boolean] => LispValue): Validation[String, LispValue] = {
    xs.map(toBool).sequenceU :-> func
  }

  def primitives: Map[String, LispOp] = Map(
    "+" -> LispOp(numOp(_, (xs => LispNumber(xs.reduce(_ + _))))),
    "-" -> LispOp(numOp(_, (xs => LispNumber(xs.reduce(_ - _))))),
    "*" -> LispOp(numOp(_, (xs => LispNumber(xs.reduce(_ * _))))),
    "/" -> LispOp(numOp(_, (xs => LispNumber(xs.reduce(_ / _))))),
    "=" -> LispOp(numOp(_, (xs => LispBool(xs.forall(_ == xs.head))))),
    "/=" -> LispOp(numOp(_, (xs => LispBool(!xs.forall(_ == xs.head))))),
    "<" -> LispOp(numOp(_, (xs => LispBool(lessThan(xs))))),
    ">" -> LispOp(numOp(_, (xs => LispBool(greaterThan(xs))))),
    "<=" -> LispOp(numOp(_, (xs => LispBool(lessThanOrEqual(xs))))),
    ">=" -> LispOp(numOp(_, (xs => LispBool(greaterThanOrEqual(xs))))),
    "&&" -> LispOp(boolOp(_, (xs => LispBool(xs.fold(true)(_ && _))))),
    "||" -> LispOp(boolOp(_, (xs => LispBool(xs.fold(true)(_ || _))))),
    "car" -> LispOp(car),
    "cdr" -> LispOp(cdr),
    "eq?" -> LispOp(eq),
    "cons" -> LispOp(cons)
  )

  def toNumber(v: LispValue): Validation[String, Int] = v match {
    case LispNumber(x) => x.success
    case x => ("Expected number, found " + x.toString + "\n").failure
  }

  def toBool(v: LispValue): Validation[String, Boolean] = v match {
    case LispBool(x) => x.success
    case x => ("Expected boolean, found " + x.toString + "\n").failure
  }

  def lessThan(ns: List[Int]): Boolean = ns match {
    case x :: y :: xs => if (x < y) lessThan(y :: xs) else false
    case _ => true
  }

  def lessThanOrEqual(ns: List[Int]): Boolean = ns match {
    case x :: y :: xs => if (x <= y) lessThanOrEqual(y :: xs) else false
    case _ => true
  }

  def greaterThan(ns: List[Int]): Boolean = ns match {
    case x :: y :: xs => if (x > y) greaterThan(y :: xs) else false
    case _ => true
  }

  def greaterThanOrEqual(ns: List[Int]): Boolean = ns match {
    case x :: y :: xs => if (x >= y) greaterThanOrEqual(y :: xs) else false
    case _ => true
  }

  def ifExpr(env: List[Map[String, LispValue]], args: List[LispValue]): Validation[String, LispValue] = {
    args match {
      case cond :: t :: f => eval(env, cond) match {
        case Success(LispBool(false)) => f match {
          case x :: Nil => eval(env, x)
          case _ => "Undefined".failure
        }
        case Success(_) => eval(env, t)
        case Failure(err) => err.failure
      }
      case _ => ("Bad if syntax: " + LispList(LispIdentifier("if") :: args)).failure
    }
  }

  def cons(args: List[LispValue]): Validation[String, LispValue] = args match {
    case x :: LispList(ys) :: Nil => LispList(x :: ys).success
    case x :: LispDottedList(ys, t) :: Nil => LispDottedList(x :: ys, t).success
    case x :: y :: Nil => LispDottedList(List(x), y).success
    case _ => ("Wrong number of arguments for cons: " + args.length).failure
  }

  def car(args: List[LispValue]): Validation[String, LispValue] = args match {
    case LispList(x :: _ :: Nil) :: Nil => x.success
    case LispDottedList(x :: _, _) :: Nil => x.success
    case _ => ("Wrong number of arguments for car: " + args.length).failure
  }

  def cdr(args: List[LispValue]): Validation[String, LispValue] = args match {
    case LispList(_ :: x) :: Nil => LispList(x).success
    case LispDottedList(_ :: Nil, x) :: Nil => x.success
    case LispDottedList(x::xs, y) :: Nil => LispDottedList(xs, y).success
    case _ => ("Wrong number of arguments for car: " + args.length).failure
  }

  def eq(args: List[LispValue]): Validation[String, LispValue] = {
    LispBool(args.forall(_.toString == args.head.toString)).success
  }

  def applyFunc(env: List[Map[String, LispValue]], func: LispValue, args: List[LispValue]):
      Validation[String, LispValue] = eval(env, func) match {
    case Success(LispOp(op)) => { op(args) }
    case Success(LispProcedure(formals, body, environment)) => {
      if (args.length < formals.length)
        ("Not enough arguments: " + args.length + ", expected " + formals.length).failure
      else if (args.length > formals.length)
        ("Too many arguments: " + args.length + ", expected " + formals.length).failure
      else {
        for {
          (formal, actual) <- formals.zip(args)
        } yield {
          setValue(environment, formal, actual)
        }
        body.map(eval(environment, _)).reverse.head
      }
    }
    case _ => ("Expected procedure call, found " + func.toString).failure
  }

  def idString(id: LispValue): Validation[String, String] = id match {
    case LispIdentifier(x) => x.success
    case _ => ("Expected identifier, found " + id.toString).failure
  }

  def getValue(env: List[Map[String, LispValue]], name: String): Validation[String, LispValue] = env match {
    case Nil => ("Variable " + name + " not found").failure
    case x :: xs => {
      if (x.contains(name))
        x(name).success
      else
        getValue(xs, name)
    }
  }

  def setValue(env: List[Map[String, LispValue]],
    name: String, value: LispValue): List[Map[String, LispValue]] = env match {
    case x :: xs => { x(name) = value; env }
    case _ => Nil
  }

  def eval(env: List[Map[String, LispValue]], expr: LispValue): Validation[String, LispValue] = expr match {
    case LispList(LispIdentifier("quote")::xs::Nil) => xs.success
    case LispList(LispIdentifier("quote")::_) => "Bad quote syntax".failure
    case LispList(LispIdentifier("if")::xs) => ifExpr(env, xs)
    case LispList(LispIdentifier("lambda")::xs) => xs match {
      case LispList(formals)::body =>
        formals.map(idString).sequenceU :-> (fs => LispProcedure(fs, body, (Map[String, LispValue]() :: env)))
      case _ => ("Bad lambda syntax").failure
    }
    case LispList(LispIdentifier("define")::LispIdentifier(name)::value::Nil) => {
      eval(env, value) match {
        case Success(v) => { setValue(env, name, v); v.success }
        case Failure(f) => f.failure
      }
    }
    case LispList(id::xs) => xs.map(eval(env, _)).sequenceU match {
      case Success(ys) => {
        eval(env, id) match {
          case Success(f @ LispOp(_)) => applyFunc(env, f, ys)
          case Success(f @ LispProcedure(_, _, _)) => applyFunc(env, f, ys)
          case _ => ("Expected identifier, found " + id).failure
        }
      }
      case Failure(f) => f.failure
    }
    case LispIdentifier(id) => {
      if (primitives.contains(id))
        primitives(id).success
      else
        getValue(env, id)
    }
    case _ => expr.success
  }
}

class Interpreter {
  val parser = new LispParser();
  val evaluator = new Evaluator();

  def interpret(line: String, env: List[Map[String, LispValue]] = List(Map())) {
    val parseResult = parser.read(line)
    parseResult match {
      case parser.Success(result, _) => {
        evaluator.eval(env, result) match {
          case Success(value) => println(value)
          case Failure(msg) => println(msg)
        }
      }
      case _ => println(parseResult)
    }
  }

  def loop() {
    val env: List[Map[String, LispValue]] = List(Map());
    while (true) {
      print("lisp> ");
      val line = readLine();
      if (line == "quit") return;
      interpret(line, env);
    }
  }
}

object Main {
  def main(args: Array[String]): Unit = {
    val lisp = new Interpreter();
    if (args.length > 0)
      lisp.interpret(args(0));
    else
      lisp.loop();
  }
}
