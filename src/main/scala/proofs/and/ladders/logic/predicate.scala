package proofs.and.ladders

package logic
package predicate

import proofs.and.ladders.logic.predicate.Quantification.ForAll
import proofs.and.ladders.logic.propositional.Equivalence.<->
import propositional.WFF
import propositional.Axioms._
import propositional.Implication._

trait Setvar

object Quantification {
  trait ForAll[X <: Setvar, P <: WFF] extends WFF

  trait Exists[X <: Setvar, P <: WFF] extends WFF
  def DfExists[X <: Setvar, P <: WFF]
  : |-[ Exists[X, P] <-> ~[ForAll[X, ~[P]]]]
  = Axiom()

  trait NotFree[X <: Setvar, P <: WFF] extends WFF
  def DfNotFree[X <: Setvar, P <: WFF]
  : |-[ NotFree[X, P] <-> ForAll[X, P -> ForAll[X, P]] ]
  = Axiom()
}

object Generalization {
  def Generalization[P <: WFF, X <: Setvar]
  (p: |-[P])
  : |-[ ForAll[X, P] ]
  = Axiom()

  def MPGen[X <: Setvar, P <: WFF, Q <: WFF]
  (maj: |-[ForAll[X, P] -> Q], min: |-[P])
  : |-[ Q ]
  = MP(Generalization[P, X](min), maj)
}

object QuantifiedImplication {

}

trait Distinct[X]

object Distinctness {

}

trait Class

object Substitution {
  def Classvar [X <: Setvar]
  (x: |-[X])
  : |-[Class]
  = Axiom()

  /*trait `=`[A <: Class, B <: Class] extends WFF
  type `=`[A <: Setvar, B <: Setvar] = `=`[A, B]
  trait `E`[X <: Setvar, Y <: Setvar] extends WFF

  trait _1 extends Class
  trait _2 extends Class
  trait Suc[A <: Class] extends Class

  def Df2
  : |-[_2 `=` Suc[_1]]
  = Axiom()*/

}

object Existence {

}

object Equality {

}

object Membership {

}