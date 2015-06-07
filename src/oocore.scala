// P ::= D ; C
// E ::= N | ( E1 + E2 ) | L | (E1 == E2) | not E | new T | nil
// C ::= L = E | if E { C1 } else { C2 } | print L | C1 ; C2 | while E { C }
// D :: var I = E | D1 ; D2
// T :: struct D end | array[N] of E
// L ::= I | L . I | L[E]
// N ::= string of digits
// I ::= strings of letters, not including keywords

trait OpTree {
  sealed abstract class Ctree
  case class Assign(l: Ltree, e: Etree) extends Ctree
  case class Cond(e: Etree, cs1: Ctree, cs2: Ctree) extends Ctree
  case class While(e: Etree, cs1: Ctree) extends Ctree
  case class Print(l: Ltree) extends Ctree
  case class Seq(cl: List[Ctree]) extends Ctree

  sealed abstract class Etree
  case class Num(s: String) extends Etree
  case class Add(e1: Etree, e2: Etree) extends Etree
  case class Sub(e1: Etree, e2: Etree) extends Etree
  case class Deref(l: Ltree) extends Etree
  case class New(xs: Ttree) extends Etree
  case class Not(e:Etree) extends Etree
  case class Bop(e:Etree,e1:Etree) extends Etree
  case class Nil_() extends Etree

  sealed abstract class Ltree
  case class Id(x: String) extends Ltree
  case class Dot(l: Ltree, x: Ltree) extends Ltree
  case class Arr(l: Ltree, e: Etree) extends Ltree

  sealed abstract class Dtree
  case class Dec(x: String, e: Etree) extends Dtree
  case class Dseq(dl: List[Dtree]) extends Dtree

  sealed abstract class Ttree
  case class St(d: Dtree) extends Ttree
  case class Ar(n: Int, e: Etree) extends Ttree
}

import scala.util.parsing.combinator.JavaTokenParsers

object oocore extends JavaTokenParsers with OpTree {

  // Parser
  def parse(source: String): (Dtree, Ctree) =
    parseAll(prog, source) match {
      case Success(optree, _) => optree
      case _ => throw new Exception("Parse error!")
    }

  def prog: Parser[(Dtree, Ctree)] =
    (defns <~ ";") ~ coms ^^ { case d ~ c => (d, c) } |
      defns ^^ { case d => (d, Seq(List())) }

  def commlist: Parser[List[Ctree]] = rep1sep(comm, ";")

  def coms: Parser[Ctree] = rep1sep(comm, ";") ^^ { case cl => Seq(cl) }
  def comm: Parser[Ctree] =
    lefts ~ ("=" ~> expr) ^^
      { case l ~ e => Assign(l, e) } |
      ("if" ~> expr <~ "{") ~ (coms<~"}" <~ "else") ~ ("{"~>coms <~ "}") ^^
      { case e ~ cs1 ~ cs2 => Cond(e, cs1, cs2) } |
      ("while" ~> expr <~ "{") ~ coms <~ "}" ^^
      { case e ~ cs1 => While(e, cs1) } |
      "print" ~> lefts ^^ (Print(_))

  def defns: Parser[Dtree] = rep1sep(defn, ";") ^^ { case dl => Dseq(dl) }
  def defn: Parser[Dtree] =
    ("var" ~> ident) ~ ("=" ~> expr) ^^ { case i ~ e => Dec(i, e) }

  def expr: Parser[Etree] =
    wholeNumber ^^ (Num(_)) |
    "not"~> expr ^^ (Not(_)) |
    ("(" ~> expr <~ "==") ~ expr <~ ")" ^^ { case e1~e2 => Bop(e1,e2)} |
      "(" ~> expr ~ op ~ expr <~ ")" ^^
      {
        case e1 ~ "+" ~ e2 => Add(e1, e2)
        case e1 ~ "-" ~ e2 => Sub(e1, e2)
      } |
      "new" ~> templ ^^ (New(_)) |
      lefts ^^ (Deref(_))

  def templ: Parser[Ttree] =
    "struct" ~> defns <~ "end" ^^ (St(_)) |
      ("array" ~> "[" ~> wholeNumber <~ "]") ~ ("of" ~> expr) ^^
      { case n ~ e => Ar(n.toInt, e) }

  def le: Parser[Ltree] =
    ident ~ rep("[" ~> expr <~ "]") ^^ {
      case l ~ el =>
        val id: Ltree = Id(l)
        (id /: el)(Arr(_, _))
    } |
      ident ^^ (Id(_))

  def lefts: Parser[Ltree] =
    rep1sep(le, ".") ^^
    {
      case h:: List() => h
      case v:: lst => (v /: lst) (Dot(_,_))
      case List() => throw new Exception("empty lhs")
    }

  def op: Parser[String] = "+" | "-"

  sealed abstract class Rval
  case class Handle(loc: Int) extends Rval
  case class Value(n: Int) extends Rval
  case object Nil extends Rval

  sealed abstract class Mem
  case class Namespace(c: Map[String, Rval]) extends Mem
  case class M_Array(n: scala.collection.mutable.ArrayBuffer[Rval]) extends Mem

  var heap: Map[Handle, Mem] = Map()

  var ns: List[Handle] = List()
  ns = List(allocateNS())

  def allocateNS(): Handle = {
    val newhandle = Handle(heap.size)
    val p = if (ns == List()) Handle(-1) else ns.head
    heap += (newhandle -> Namespace(Map("parents" -> p)))
    newhandle
  }

  def heap_of_loc(m: Mem): Map[String, Rval] = m match {
    case Namespace(l) => l
    case _ => throw new Exception("not Namespace")
  }

  def lookup(lval: (Handle, String, Int)): Rval = {
    val (handle, fieldname, i) = lval
    heap(handle) match {
      case Namespace(m) =>
        if ((heap contains handle))
          heap_of_loc(heap(handle))(fieldname)
        else
          throw new Exception("lookup error: "+handle+ " Not contains "+ fieldname)
      case M_Array(a) => a(i)
    }
  }

  def store(lval: (Handle, String, Int), rval: Rval): Unit = {
    val (handle, fieldname, i) = lval
    heap(handle) match {
      case Namespace(m) =>
        if (heap contains handle) {
          heap += (handle -> Namespace((heap_of_loc(heap(handle)) + (fieldname -> rval))))
        } else // if the handle is not in the heap
          throw new Exception("bind error: " + handle + " does not exist in the heap")
      case M_Array(a) =>{
          a(i) = rval
          heap += (handle -> M_Array(a))
      }
    }
  }

  def find(lval: (Handle, String)): Handle = {
    val (han, x) = lval
    if (heap_of_loc(heap(han)) contains x) han
    else {
      heap_of_loc(heap(han))("parents") match {
        case Handle(h) =>
          if (Handle(h) == Handle(-1)) throw new Exception("find error not found " + x)
          else find((Handle(h), x))
        case _ => throw new Exception("This case will never be selected.(find parents)")
      }
    }
  }
  // Interpreter

  def interpretPTREE(p: (Dtree, Ctree)): Unit = {
    val (d, c) = p
    interpretDTREE(d)
    interpretCTREE(c)
  }

  def interpretDTREE(d: Dtree): Unit = d match {
    case Dec(x, e) => {
      store((ns.head, x, -1), interpretETREE(e))
    }
    case Dseq(ds) => for (d <- ds) interpretDTREE(d)
  }
  
  def interpretTTREE(t: Ttree): Unit = t match {
    case St(d) =>
      //write the code
      interpretDTREE(d)
      
    case Ar(n, e) =>
      //write the code
      val array = new scala.collection.mutable.ArrayBuffer[Rval]
      for(i <- 1 to n)
        array.append(interpretETREE(e))
      heap += (ns.head -> M_Array(array))
  }
  
  def interpretCLIST(cs: List[Ctree]): Unit =
    for (c <- cs) yield interpretCTREE(c)

  def interpretCTREE(c: Ctree): Unit = c match {
    case Assign(l, e) => {
      store(interpretLTREE(l,ns.head), interpretETREE(e))
    }
    case Cond(e, cs1, cs2) =>
      interpretETREE(e) match {
        case Value(n) => if (n != 0) interpretCTREE(cs1)
        else interpretCTREE(cs2)
        case _ => throw new Exception
      }
    case While(e, cs1) =>
      interpretETREE(e) match {
        case Value(n) =>
          if (n != 0) {
            interpretCTREE(cs1)
            interpretCTREE(c)
          }
        case _ => throw new Exception
      }
    case Print(l) => {
      println(lookup(interpretLTREE(l,ns.head)))
    }
    case Seq(cs) => for (c <- cs) yield interpretCTREE(c)
  }

  def interpretETREE(e: Etree): Rval = e match {
    case Nil_() => Nil
    case Bop(e1,e2)=>{
      if (interpretETREE(e1)==interpretETREE(e2)) Value(1) else Value(0)
    }
    case Not(e) =>{
      interpretETREE(e) match {
        case Value(n) =>
          if (n==1) Value(0) else Value(1)
        case _ => throw new Exception
      }
    }

    case Num(n) => Value(n.toInt)
    case Add(e1, e2) => {
      val n1 = interpretETREE(e1) match {
        case Value(n) => n
        case _ => throw new Exception (e1+" is not value")
      }
      val n2 = interpretETREE(e2) match {
        case Value(n) => n
        case _ => throw new Exception (e2+" is not value")
      }
      Value(n1 + n2)
    }
    case Sub(e1, e2) =>
      {
        val n1 = interpretETREE(e1) match {
          case Value(n) => n
          case _ => throw new Exception (e1+" is not value")
        }
        val n2 = interpretETREE(e2) match {
          case Value(n) => n
          case _ => throw new Exception (e2+" is not value")
        }
        Value(n1 - n2)
      }
    case Deref(l) => {
      lookup(interpretLTREE(l,ns.head))
    }
    case New(t) => {
      //write the code
      val handle = allocateNS()
      ns = List(handle) ++ ns
      interpretTTREE(t)
      ns = ns.tail
      handle
    }
  }

  def interpretLTREE(left: Ltree, han1: Handle): (Handle, String, Int) = {
    left match {
      case Id(x) => {
        (find(han1, x), x, -1)
      }
      case Dot(ls, l1) => {
        //write the code
        val (han2, x1, i1) = interpretLTREE(ls, han1) 
        lookup(han2, x1, i1) match {
          case Handle(h) =>
            val (han3, x2, i2) = interpretLTREE(l1, Handle(h))
            heap(Handle(h)) match {
              case M_Array(a) => (han3, x2, i2)
              case Namespace(m) =>
                if(m contains x2) (han3, x2, i2)
                else throw new Exception("Not member " + x2)
            }
          case Value(n) => throw new Exception("")
          case Nil => throw new Exception("")
        }
      }
      case Arr(l, e) => {
        //write the code
        val (han2, x, i) = interpretLTREE(l, han1)
        lookup((han2, x, i)) match {
          case Handle(h) => (Handle(h), x, interpretETREE(e) match {
            case Value(n) => n
            case Handle(h) => throw new Exception("")
            case Nil => throw new Exception("")
          })
          case Value(e) => throw new Exception("")
          case Nil => throw new Exception("")
        }
      }
    }
  }

  def main(args: Array[String]): Unit = {
    try {
     val source = args(0)
      println("input : " + source)
      val optree = parse(source)
      println("optree : " + optree)
      interpretPTREE(optree)
      println("namespace : " + ns)
      println("heap : " + heap)
    } catch { case e: Exception => println(e) }
  }
}

//example 1 (0.5point)
//input : var x =3; var z = new struct var f =0; var g = 1 end; var r = new array[4] of 0;r[3]=100;print r[3]
//optree : (Dseq(List(Dec(x,Num(3)), Dec(z,New(St(Dseq(List(Dec(f,Num(0)), Dec(g,Num(1))))))), Dec(r,New(Ar(4,Num(0)))))),Seq(List(Assign(Arr(Id(r),Num(3)),Num(100)), Print(Arr(Id(r),Num(3))))))
//Value(100)
//namespace : List(Handle(0))
//heap : Map(Handle(0) -> Namespace(Map(parents -> Handle(-1), x -> Value(3), z -> Handle(1), r -> Handle(2))), Handle(1) -> Namespace(Map(parents -> Handle(0), f -> Value(0), g -> Value(1))), Handle(2) -> M_Array(ArrayBuffer(Value(0), Value(0), Value(0), Value(100))))

//example 2 (0.5point)
//input : var x =3; var z = new struct var f =0; var g = 1 end; var r = new array[4] of 0;z.x=30
//optree : (Dseq(List(Dec(x,Num(3)), Dec(z,New(St(Dseq(List(Dec(f,Num(0)), Dec(g,Num(1))))))), Dec(r,New(Ar(4,Num(0)))))),Seq(List(Assign(Dot(Id(z),Id(x)),Num(30)))))
//java.lang.Exception: Not member x

//example 3 (0.5point)
//input : var x = 7;var y = new array[4] of new array[4] of 3;y[3][3]=120;print y[3][3]
//optree : (Dseq(List(Dec(x,Num(7)), Dec(y,New(Ar(4,New(Ar(4,Num(3)))))))),Seq(List(Assign(Arr(Arr(Id(y),Num(3)),Num(3)),Num(120)), Print(Arr(Arr(Id(y),Num(3)),Num(3))))))
//Value(120)
//namespace : List(Handle(0))
//heap : Map(Handle(0) -> Namespace(Map(parents -> Handle(-1), x -> Value(7), y -> Handle(1))), Handle(4) -> M_Array(ArrayBuffer(Value(3), Value(3), Value(3), Value(3))), Handle(1) -> M_Array(ArrayBuffer(Handle(2), Handle(3), Handle(4), Handle(5))), Handle(3) -> M_Array(ArrayBuffer(Value(3), Value(3), Value(3), Value(3))), Handle(5) -> M_Array(ArrayBuffer(Value(3), Value(3), Value(3), Value(120))), Handle(2) -> M_Array(ArrayBuffer(Value(3), Value(3), Value(3), Value(3))))

//example 4 (0.5point)
//input : var x =3; var z = new struct var f =0; var g = 1 end; var r = new array[4] of 0;if not (z.g == z.f) { print z.f} else {print x}
//optree : (Dseq(List(Dec(x,Num(3)), Dec(z,New(St(Dseq(List(Dec(f,Num(0)), Dec(g,Num(1))))))), Dec(r,New(Ar(4,Num(0)))))),Seq(List(Cond(Not(Bop(Deref(Dot(Id(z),Id(g))),Deref(Dot(Id(z),Id(f))))),Seq(List(Print(Dot(Id(z),Id(f))))),Seq(List(Print(Id(x))))))))
//Value(0)
//namespace : List(Handle(0))
//heap : Map(Handle(0) -> Namespace(Map(parents -> Handle(-1), x -> Value(3), z -> Handle(1), r -> Handle(2))), Handle(1) -> Namespace(Map(parents -> Handle(0), f -> Value(0), g -> Value(1))), Handle(2) -> M_Array(ArrayBuffer(Value(0), Value(0), Value(0), Value(0))))

//example 5 (1point)
//input : var x = 7;var y = new array[4] of new struct var a=10 end;y[3].a = 100
//optree : (Dseq(List(Dec(x,Num(7)), Dec(y,New(Ar(4,New(St(Dseq(List(Dec(a,Num(10))))))))))),Seq(List(Assign(Dot(Arr(Id(y),Num(3)),Id(a)),Num(100)))))
//namespace : List(Handle(0))
//heap : ? ? ?

//example 6 (1point)
//input : var x =3; var z = new struct var y = new array [3] of new struct var a =10 end end;z.y[1].a=100; print z.y[0].a
//optree : (Dseq(List(Dec(x,Num(3)), Dec(z,New(St(Dseq(List(Dec(y,New(Ar(3,New(St(Dseq(List(Dec(a,Num(10)))))))))))))))),Seq(List(Assign(Dot(Dot(Id(z),Arr(Id(y),Num(1))),Id(a)),Num(100)), Print(Dot(Dot(Id(z),Arr(Id(y),Num(0))),Id(a))))))
//Value(10)
//namespace : List(Handle(0))
//heap : ? ? ?

//example 7 (1point)
//input : var x = 1;var y = new array[2] of new array[2] of new array[2] of new struct var a=x end;y[1][(x-1)][1].a = 100
//optree : (Dseq(List(Dec(x,Num(1)), Dec(y,New(Ar(2,New(Ar(2,New(Ar(2,New(St(Dseq(List(Dec(a,Deref(Id(x)))))))))))))))),Seq(List(Assign(Dot(Arr(Arr(Arr(Id(y),Num(1)),Sub(Deref(Id(x)),Num(1))),Num(1)),Id(a)),Num(100)))))
//namespace : List(Handle(0))
//heap : ? ? ?