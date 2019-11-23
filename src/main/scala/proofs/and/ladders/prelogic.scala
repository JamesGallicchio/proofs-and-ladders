package proofs.and.ladders

sealed trait |-[T] {
  def axioms: Set[Axiom[_]]
  def definitions: Set[Definition[_]]
}

case class Axiom[T](name: String = (new Exception).getStackTrace()(1).getMethodName,
                    private val parentAxioms: Set[Axiom[_]] = Set.empty,
                    private val parentDefs: Set[Definition[_]] = Set.empty) extends |-[T] { self =>
  override def axioms: Set[Axiom[_]] = parentAxioms + self
  override def definitions: Set[Definition[_]] = parentDefs
  override def toString: String = s"Axiom($name)"
}

case class Definition[T](name: String = (new Exception).getStackTrace()(1).getMethodName) extends |-[T] { self =>
  override def axioms: Set[Axiom[_]] = Set.empty
  override def definitions: Set[Definition[_]] = Set(self)
  override def toString: String = s"Def($name)"
}

object Placeholder {
  def apply[T](): |-[T] = Axiom("placeholder")
}
