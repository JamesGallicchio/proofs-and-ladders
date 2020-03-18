package proofs.and.ladders

import scala.annotation.showAsInfix

@showAsInfix
sealed trait |-[T] {
  def axioms: Set[Axiom]
  def proof: (Axiom, Seq[|-[_]])
  def proofString: String = {
    val (a, hs) = proof
    s"$a(${hs.map(_.proofString).mkString(",")})"
  }
}

trait Axiom { self =>
  def ax[T](hypotheses: Seq[|-[_]] = Seq.empty): |-[T] =
    new |-[T] {
      override def axioms: Set[Axiom] =
        hypotheses.map(_.axioms).foldLeft(Set.empty[Axiom])(_ ++ _) + self
      override def proof: (Axiom, Seq[|-[_]]) =
        (self, hypotheses)
    }
  override def toString: String = self.getClass.getSimpleName
}

object Placeholder extends Axiom {
  def apply[T](): |-[T] = ax()
}
