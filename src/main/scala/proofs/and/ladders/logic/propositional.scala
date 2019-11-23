package proofs.and.ladders

package logic
package propositional

trait WFF

object Axioms {

  trait ~   [L <: WFF] extends WFF
  trait ->  [L <: WFF, R <: WFF] extends WFF

  def Simp [P <: WFF, Q <: WFF]
  : |-[ P -> (Q -> P) ]
  = Axiom()

  def Dist [P <: WFF, Q <: WFF, R <: WFF]
  : |-[ (P -> (Q -> R)) -> ((P -> Q) -> (P -> R)) ]
  = Axiom()

  def Trans [P <: WFF, Q <: WFF]
  : |-[ (~[P] -> ~[Q]) -> (Q -> P) ]
  = Axiom()

  def MP [P <: WFF, Q <: WFF]
  (min: |-[P], maj: |-[P -> Q])
  : |-[ Q ]
  = Axiom(parentAxioms = min.axioms ++ maj.axioms)
}

object Implication {
  import Axioms.{->, Dist, Simp, MP}

  def SimpInf [P <: WFF, Q <: WFF]
  (_1: |-[P])
  : |-[Q -> P]
  = MP(_1, Simp)

  def DistInf [P <: WFF, Q <: WFF, R <: WFF]
  (_1: |-[P -> (Q -> R)])
  : |-[ (P -> Q) -> (P -> R) ]
  = MP(_1, Dist)

  def MPDouble [P <: WFF, Q <: WFF, R <: WFF]
  (_1: |-[P], _2: |-[Q], _3: |-[P -> (Q -> R)])
  : |-[R]
  = MP(_2, MP(_1, _3))

  def MPDed [P <: WFF, Q <: WFF, R <: WFF]
  (min: |-[P -> Q], maj: |-[P -> (Q -> R)])
  : |-[ P -> R ]
  = {
    val _1: |-[ (P -> Q) -> (P -> R) ] = DistInf(maj)
    MP(min, _1)
  }

  def MPDedMin [P <: WFF, Q <: WFF, R <: WFF]
  (_1: |-[P -> Q], _2: |-[Q -> R])
  : |-[P -> R]
  = {
    val _3: |-[P -> (Q -> R)] = SimpInf(_2)
    MPDed(_1, _3)
  }

  def MPDedMaj [P <: WFF, Q <: WFF, R <: WFF]
  (min: |-[Q], maj: |-[ P -> (Q -> R) ])
  : |-[ P -> R ]
  = {
    val _1: |-[ P -> Q ] = SimpInf(min)
    MPDed(_1, maj)
  }

  def SimpDed [P <: WFF, Q <: WFF, R <: WFF]
  (_1: |-[P -> Q])
  : |-[ P -> (R -> Q) ]
  = {
    val _2: |-[Q -> (R -> Q)] = Simp
    MPDedMin(_1, _2)
  }

  def Identity [P <: WFF]
  : |-[ P -> P ]
  = {
    val _1: |-[P -> (P -> P)] = Simp
    val _2: |-[P -> ((P -> P) -> P)] = Simp
    MPDed(_1, _2)
  }

  def Flatten [P <: WFF, Q <: WFF]
  (_1: |-[ P -> (P -> Q) ])
  : |-[ P -> Q ]
  = MPDed(Identity, _1)

}

object Negation {
  import Axioms._
  import Implication._

  def TransInf [P <: WFF, Q <: WFF]
  (_1: |-[ (~[P] -> ~[Q]) ])
  : |-[ Q -> P ]
  = MP(_1, Trans)

  def TransDed [P <: WFF, Q <: WFF, R <: WFF]
  (_1: |-[ P -> (~[Q] -> ~[R]) ])
  : |-[ P -> (R -> Q) ]
  = {
    val _2: |-[ (~[Q] -> ~[R]) -> (R -> Q) ] = Trans
    MPDedMin(_1, _2)
  }

  def FalsePrem [P <: WFF, Q <: WFF]
  : |-[ ~[P] -> (P -> Q) ]
  = {
    val _1: |-[ ~[P] -> (~[Q] -> ~[P]) ] = Simp
    TransDed(_1)
  }

  def NotNot [P <: WFF]
  : |-[ ~[~[P]] -> P ]
  = ???

  def NotNotRev[P <: WFF]
  : |-[ P -> ~[~[P]] ]
  = {
    val _1: |-[ ~[~[~[P]]] -> ~[P] ] = NotNot
    TransInf(_1)
  }

  def TransRev [P <: WFF, Q <: WFF]
  : |-[ (P -> Q) -> (~[Q] -> ~[P]) ]
  = {
    val _1: |-[ (P -> Q) -> (P -> Q)  ] = Identity
    val _2: |-[ P -> ~[~[P]] ] = NotNotRev
    //val _3: |-[_] = ???
    //val _2: |-[ ~[~[P]] -> Q ] = MPDed2(NotNot, _1)
    //val _2: |-[ ~[~[P]] -> ~[~[Q]] ] = MPDed2(_1, NotNotRev)
    //TransInf(_2)
    ???
  }

  def TransRevInf [P <: WFF, Q <: WFF]
  (_1: |-[ P -> Q ])
  : |-[ ~[Q] -> ~[P] ]
  = {
    val _2: |-[ ~[~[P]] -> Q ] = MPDedMin(NotNot, _1)
    val _3: |-[ ~[~[P]] -> ~[~[Q]] ] = MPDedMin(_2, NotNotRev)
    TransInf(_3)
  }

  def TransRevDed [P <: WFF, Q <: WFF, R <: WFF]
  (_1: |-[ P -> (Q -> R) ])
  : |-[ P -> (~[R] -> ~[Q]) ]
  = ???

  def NotImplyPrem [P <: WFF, Q <: WFF]
  : |-[ ~[P -> Q] -> P ]
  = {
    val _1: |-[ P -> (Q -> P) ] = Simp
    val _2: |-[ P -> (~[P] -> ~[Q]) ] = TransRevDed(_1)
    //val _2: |-[  -> P ] = NotNot
    ???
  }

  def NotImplyConc [P <: WFF, Q <: WFF]
  : |-[ ~[P -> Q] -> ~[Q] ]
  = {
    val _1: |-[ Q -> (P -> Q) ] = Simp
    TransRevInf(_1)
  }

}

object Equivalence {
  import Axioms._
  import Implication._
  import Negation._

  trait <-> [L <: WFF, R <: WFF] extends WFF
  def DfBi [P <: WFF, Q <: WFF]
  : |-[ ~[ (P <-> Q) -> ~[(P -> Q) -> ~[Q -> P]]
    ->  ~[ ~[(P -> Q) -> ~[Q -> P]] -> (P <-> Q) ]] ]
  = Definition()

  def BiImply [P <: WFF, Q <: WFF]
  : |-[(P <-> Q) -> (P -> Q)]
  = ???

  def BiInf [P <: WFF, Q <: WFF]
  (_1: |-[P -> Q], _2: |-[Q -> P])
  : |-[ P <-> Q ]
  = {
    val _3: |-[P -> (Q -> P)] = Simp
    Placeholder()
  }

  def BiIdentity [P <: WFF]
  : |-[ P <-> P ]
  = {
    val id: |-[P -> P] = Identity
    BiInf(id, id)
  }

  def BiComm [P <: WFF, Q <: WFF]
  : |-[ (P <-> Q) <-> (Q <-> P) ]
  = ???

  def BiTransi [P <: WFF, Q <: WFF, R <: WFF]
  (_1: |-[P <-> Q], _2: |-[Q <-> R])
  : |-[ P <-> R ]
  = ???
}

/**
  * Introduce logical conjunction and disjunction
  */
object Junction {
  import Axioms._
  import Implication._
  import Negation._
  import Equivalence._

  trait &   [L <: WFF, R <: WFF] extends WFF
  trait |   [L <: WFF, R <: WFF] extends WFF

  def DfOr [P <: WFF, Q <: WFF]
  : |-[ (P | Q) <-> (~[P] -> Q) ]
  = Axiom()

  def OrComm [P <: WFF, Q <: WFF]
  : |-[ (P | Q) <-> (Q | P) ]
  = {
    val _1: |-[ (P | Q) <-> (~[P] -> Q) ] = DfOr
    ???
  }
}

object Truth {
  import Axioms._

  trait T extends WFF
  trait F extends WFF
}