// P ::= D ; C
// E ::= N | ( E1 + E2 ) | L | (E1 == E2) | not E | new T | nil
// C ::= L = E | if E { C1 } else { C2 } | print L | C1 ; C2 | while E { C } | L()
// D :: var I = E | D1 ; D2 | proc I() { C }
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
  case class Func(l: Ltree) extends Ctree

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
  case class Proc(x: String, cl: List[Ctree]) extends Dtree
  case class Tclass(x: String, t: Ttree) extends Dtree
  case class Module(x: String, dl: Dtree) extends Dtree
  case class Import(l: Ltree) extends Dtree

  sealed abstract class Ttree
  case class St(d: Dtree) extends Ttree
  case class Ar(n: Int, e: Etree) extends Ttree
  case class Cl(l: Ltree) extends Ttree
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
    lefts ~ ("=" ~> expr) ^^ { case l ~ e => Assign(l, e) } |
    ("if" ~> expr <~ "{") ~ (coms<~"}" <~ "else") ~ ("{"~>coms <~ "}") ^^ { case e ~ cs1 ~ cs2 => Cond(e, cs1, cs2) } |
    ("while" ~> expr <~ "{") ~ coms <~ "}" ^^ { case e ~ cs1 => While(e, cs1) } |
    "print" ~> lefts ^^ (Print(_)) |
    lefts <~ "()" ^^ (Func(_))

  def defns: Parser[Dtree] = rep1sep(defn, ";") ^^ { case dl => Dseq(dl) }
  def defn: Parser[Dtree] =
    ("var" ~> ident) ~ ("=" ~> expr) ^^ { case i ~ e => Dec(i, e) } |
    ("proc" ~> ident <~ "()" ) ~ ( "{" ~> commlist <~ "}") ^^ { case i ~ cl => Proc(i, cl) } |
    ("class" ~> ident) ~ ("=" ~> templ) ^^ { case i ~ t => Tclass(i, t) } |
    ("module" ~> ident) ~ ("=" ~> defns <~ "end") ^^ { case i ~ dl => Module(i, dl)} |
    ("import" ~> le) ^^ { case l => Import(l)}

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
    ("array" ~> "[" ~> wholeNumber <~ "]") ~ ("of" ~> expr) ^^ { case n ~ e => Ar(n.toInt, e) } |
    lefts ^^ (Cl(_))

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
  case class Closure(cl: List[Ctree], p: Rval) extends Mem 
  case class TClosure(t: Ttree, p: Rval) extends Mem
  case class MClosure(dl: Dtree, p: Rval) extends Mem

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
      case _ => throw new Exception
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
      case _ => throw new Exception
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
    case Dec(x, e) => store((ns.head, x, -1), interpretETREE(e))
    case Dseq(ds) => for (d <- ds) interpretDTREE(d)
    
    // Procedure
    case Proc(x, cl) => {
       val newhandle = Handle(heap.size)
       val p = if (ns == List()) Handle(-1) else ns.head
       heap += (newhandle -> Closure(cl, p))
       store((ns.head, x, -1), newhandle)
    }
    
    // Class
    case Tclass(x, t) => {
      val newhandle = Handle(heap.size)
      val p = if(ns == List()) Handle(-1) else ns.head
      heap += (newhandle -> TClosure(t, p))
      store((ns.head, x, -1), newhandle)
    }
    
    // Module
    case Module(x, dl) => {
      val newhandle = Handle(heap.size)
      val p = if(ns == List()) Handle(-1) else ns.head
      heap += (newhandle -> MClosure(dl, p))
      store((ns.head, x, -1), newhandle)
    }
    case Import(l) => {
      var (handle, x, _) = interpretLTREE(l, ns.head)
      lookup(handle,x,-1) match {
        case Handle(h) => {
           heap(Handle(h)) match {
              case MClosure(dl, p) => interpretDTREE(dl)
              case _ => throw new Exception(x+" is not module")
           }
        }
        case _ => throw new Exception(x+" is not module")
      }
    } 
  }
  
  def interpretTTREE(t: Ttree): Unit = t match {
    case St(d) =>
      interpretDTREE(d)
      
    case Ar(n, e) => {
      val array = new scala.collection.mutable.ArrayBuffer[Rval]
      for(i <- 1 to n)
        array.append(interpretETREE(e))
      heap += (ns.head -> M_Array(array))
    }
    
    // Class
    case Cl(l) => {
      var (handle, x, _) = interpretLTREE(l, ns.head)
      lookup(handle,x,-1) match {
        case Handle(h) => {
           heap(Handle(h)) match {
              case TClosure(t, p) => interpretTTREE(t)
              case _ => throw new Exception(x+" is not class")
           }
        }
        case _ => throw new Exception(x+" is not class")
      }
    } 
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
    
    // Procedure
    case Func(l) => {
      var (handle, x, _) = interpretLTREE(l, ns.head)
      lookup(handle,x,-1) match {
        case Handle(h) =>
          {
            heap(Handle(h)) match {
              case Closure(cl, p) => {
                val newhandle = Handle(heap.size)
                heap += (newhandle -> Namespace(Map("parents" -> p)))
                ns = List(newhandle) ++ ns;
                interpretCLIST(cl)
                ns = ns.tail;
                }
              case _ => throw new Exception(x+" is not procedure")
            }
          }
        case _ => throw new Exception(x+" is not procedure")
      }
    }
    
    
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
        val (han2, x1, i1) = interpretLTREE(ls, han1) 
        lookup(han2, x1, i1) match {
          case Handle(h) =>
            val (han3, x2, i2) = interpretLTREE(l1, Handle(h))
            heap(Handle(h)) match {
              case M_Array(a) => (han3, x2, i2)
              case Namespace(m) =>
                if(m contains x2) (han3, x2, i2)
                else throw new Exception("Not member " + x2)
                
              // Procedure & Class
              case Closure(_,_) => (han3, x2, i2)
              case TClosure(_,_) => (han3, x2, i2)
            }
          case Value(n) => throw new Exception("")
          case Nil => throw new Exception("")
        }
      }
      case Arr(l, e) => {
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