
sealed abstract class PropositionalLogic

case class And(x: PropositionalLogic, y: PropositionalLogic) extends PropositionalLogic
case class Not(x: PropositionalLogic) extends PropositionalLogic
case class Or(x: PropositionalLogic, y: PropositionalLogic) extends PropositionalLogic
case class Implies(x: PropositionalLogic, y: PropositionalLogic) extends PropositionalLogic
case class Literal(id: String) extends PropositionalLogic
case class Bool(boolean: Boolean) extends PropositionalLogic


object SAT extends App {

  // Here we can write up any sentence in propositional logic and the reduction function, reduces it symbolically as
  // simply as possible to CNF or DNF.

  // isSatisfiable will determine if a sentence can be satisfied with some assignment. The idea is that we can
  // hopefully eliminate a number of propositional atoms we need to check through symbolic manipulation before doing
  // the expensive satisfiability check exhaustively.

  // SAT is NP-complete

  val p = Literal("p")
  val q = Literal("q")
  val r = Literal("r")
  val propositionalAtoms = List(p, q, r)

  val exp = Or(Implies(r, And(p, Not(Or(Not(q), q)))), Bool(false))
  val reducedExp = reduction(exp)

  println(exp)
  println(reducedExp)
  println(isSatisfiable(propositionalAtoms, reducedExp))

  def replaceAllLiterals(id: String, bool: Bool, propositionalLogic: PropositionalLogic): PropositionalLogic = {
    propositionalLogic match {
      case And(Literal(literalId), y) if literalId == id => And(bool, y)
      case And(x, Literal(literalId)) if literalId == id => And(x, bool)
      case Not(Literal(literalId)) if literalId == id => Not(bool)
      case Or(Literal(literalId), y) if literalId == id => And(bool, y)
      case Or(x, Literal(literalId)) if literalId == id => And(x, bool)
      case Implies(Literal(literalId), y) if literalId == id => And(bool, y)
      case Implies(x, Literal(literalId)) if literalId == id => And(x, bool)
      case Literal(literalId) if literalId == id => bool
      case And(x, y) => And(replaceAllLiterals(id, bool, x), replaceAllLiterals(id, bool, y))
      case Or(x, y) => Or(replaceAllLiterals(id, bool, x), replaceAllLiterals(id, bool, y))
      case Implies(x, y) => Implies(replaceAllLiterals(id, bool, x), replaceAllLiterals(id, bool, y))
      case Not(x) => Not(replaceAllLiterals(id, bool, x))
      case e => e
    }
  }

  def isTrue(propositionalLogic: PropositionalLogic): Boolean = {
    propositionalLogic match {
      case Bool(b) => b
      case _ => false
    }
  }

  def isSatisfiable(literals: List[Literal], propositionalLogic: PropositionalLogic): Boolean = {
    val booleans : List[Bool] = List(Bool(true), Bool(false))
    for (Literal(id) <- literals; boolean <- booleans) {
        val reducedReplacement = reduction(replaceAllLiterals(id, boolean, propositionalLogic))
        if (isTrue(reducedReplacement)) {
          return true
        }
    }
    false
  }

  def reduction (propositionalLogic: PropositionalLogic): PropositionalLogic = {
    propositionalLogic match {
      case And(x, y) => reduction(x) match {
        case rx@Bool(b) if !b => rx
        case Bool(b) if b => reduction(y)
        case rx@Literal(idx) => reduction(y) match {
          case ry@Literal(idy) if idy == idx => ry
          case ry@Literal(idy) if idy != idx => And(rx, ry)
          case Not(Literal(idy)) if idy == idx => Bool(false)
          case Bool(by) if by => rx
          case ry@Bool(by) if !by => ry
          case ry => And(rx, ry)
        }
        case rx@Not(_) => reduction(And(y, rx))
        case rx => And(rx, reduction(y))
      }
      case Not(x) => reduction(x) match {
        case Not(bx) => bx
        case Bool(bx) => Bool(!bx)
        case r => Not(r)
      }

      case Or(x, y) => reduction(x) match {
        case rx@Bool(b) if b => rx
        case Bool(b) if !b => reduction(y)
        case rx@Literal(idx) => reduction(y) match {
          case ry@Literal(idy) if idy == idx => ry
          case ry@Literal(idy) if idy != idx => Or(rx, ry)
          case Not(Literal(idy)) if idy == idx => Bool(true)
          case ry@Bool(b) if b => ry
          case Bool(b) if !b => rx
          case ry => And(rx, ry)
        }
        case rx@Not(_) => reduction(Or(y, rx))
        case rx => Or(rx, reduction(y))
      }

      case Implies(x, y) => reduction(Or(Not(x), y))
      case _ => propositionalLogic

    }
  }

}
