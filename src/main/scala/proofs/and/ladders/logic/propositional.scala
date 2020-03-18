package proofs.and.ladders

package logic
package propositional

import scala.annotation.showAsInfix

trait WFF

object Axioms {

  @showAsInfix
  trait ~   [L <: WFF] extends WFF
  @showAsInfix
  trait ->  [L <: WFF, R <: WFF] extends WFF

  object Simp extends Axiom {
    def apply [P <: WFF, Q <: WFF]()
    : |-[ P -> (Q -> P) ]
    = ax()
  }

  object Dist extends Axiom {
    def apply[P <: WFF, Q <: WFF, R <: WFF]()
    : |-[(P -> (Q -> R)) -> ((P -> Q) -> (P -> R))]
    = ax()
  }

  object Trans extends Axiom {
    def apply[P <: WFF, Q <: WFF]()
    : |-[(~[P] -> ~[Q]) -> (Q -> P)]
    = ax()
  }

  object MP extends Axiom {
    def apply[P <: WFF, Q <: WFF]
    (min: |-[P], maj: |-[P -> Q])
    : |-[Q]
    = ax(Seq(min, maj))
  }
}

object Implication {
  import Axioms.{->, Dist, Simp, MP}

  def SimpInf [P <: WFF, Q <: WFF]
  (_1: |-[P])
  : |-[Q -> P]
  = MP(_1, Simp())

  def DistInf [P <: WFF, Q <: WFF, R <: WFF]
  (_1: |-[P -> (Q -> R)])
  : |-[ (P -> Q) -> (P -> R) ]
  = MP(_1, Dist())

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
    val _2: |-[Q -> (R -> Q)] = Simp()
    MPDedMin(_1, _2)
  }

  def Identity [P <: WFF]
  : |-[ P -> P ]
  = {
    val _1: |-[P -> (P -> P)] = Simp()
    val _2: |-[P -> ((P -> P) -> P)] = Simp()
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
  = MP(_1, Trans())

  def TransDed [P <: WFF, Q <: WFF, R <: WFF]
  (_1: |-[ P -> (~[Q] -> ~[R]) ])
  : |-[ P -> (R -> Q) ]
  = {
    val _2: |-[ (~[Q] -> ~[R]) -> (R -> Q) ] = Trans()
    MPDedMin(_1, _2)
  }

  def FalsePrem [P <: WFF, Q <: WFF]
  : |-[ ~[P] -> (P -> Q) ]
  = {
    val _1: |-[ ~[P] -> (~[Q] -> ~[P]) ] = Simp()
    TransDed(_1)
  }

  def NotNot [P <: WFF]
  : |-[ ~[~[P]] -> P ]
  = {
    val _1: |-[ ~[~[P]] -> ((P -> P) -> P) ] = {
      val _1a: |-[ ~[~[P]] -> (~[P] -> ~[P -> P]) ] = FalsePrem[~[P], ~[P -> P]]
      val _2a: |-[ (~[P] -> ~[P -> P]) -> ((P -> P) -> P) ] = Trans()
      MPDedMin(_1a, _2a)
    }
    MPDedMaj(Identity[P], _1)
  }

  def NotNotRev[P <: WFF]
  : |-[ P -> ~[~[P]] ]
  = {
    val _1: |-[ ~[~[~[P]]] -> ~[P] ] = NotNot
    TransInf(_1)
  }

  def TransRev [P <: WFF, Q <: WFF]
  : |-[ (P -> Q) -> (~[Q] -> ~[P]) ]
  = {
    val _1: |-[ (P -> Q) -> (~[~[P]] -> ~[~[Q]]) ] = {
      val _a: |-[ (P -> Q) -> (P -> ~[~[Q]]) ] = {
        val _i: |-[ P -> (Q -> (~[~[Q]])) ] = SimpInf(NotNotRev)
        DistInf(_i)
      }
      val _b: |-[ (P -> ~[~[Q]]) -> (~[~[P]] -> ~[~[Q]]) ] = {
        val _i: |-[ ~[~[P]] -> P ] = NotNot
        val _ii: |-[ (~[~[P]] -> (P -> ~[~[Q]])) -> ((~[~[P]] -> P) -> (~[~[P]] -> ~[~[Q]])) ] = Dist()
        val _iii: |-[ (~[~[P]] -> (P -> ~[~[Q]])) -> (~[~[P]] -> ~[~[Q]]) ] = MPDedMaj(_i, _ii)
        val _iv: |-[ (P -> ~[~[Q]]) -> (~[~[P]] -> (P -> ~[~[Q]])) ] = Simp()
        MPDedMin(_iv, _iii)
      }
      MPDedMin(_a, _b)
    }
    val _2: |-[ (~[~[P]] -> ~[~[Q]]) -> (~[Q] -> ~[P]) ] = Trans()
    MPDedMin(_1, _2)
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
  = Placeholder()

  def NotImplyPrem [P <: WFF, Q <: WFF]
  : |-[ ~[P -> Q] -> P ]
  = {
    val _1: |-[ P -> (Q -> P) ] = Simp()
    val _2: |-[ P -> (~[P] -> ~[Q]) ] = TransRevDed(_1)
    //val _2: |-[  -> P ] = NotNot
    Placeholder()
  }

  def NotImplyConc [P <: WFF, Q <: WFF]
  : |-[ ~[P -> Q] -> ~[Q] ]
  = {
    val _1: |-[ Q -> (P -> Q) ] = Simp()
    TransRevInf(_1)
  }

}

object Equivalence {
  import Axioms._
  import Implication._
  import Negation._

  @showAsInfix
  trait <-> [L <: WFF, R <: WFF] extends WFF
  object DfBi extends Axiom {
    def apply[P <: WFF, Q <: WFF]()
    : |-[ ~[(P <-> Q) -> ~[(P -> Q) -> ~[Q -> P]]
            -> ~[~[(P -> Q) -> ~[Q -> P]] -> (P <-> Q)]] ]
    = ax()
  }

  def BiImply [P <: WFF, Q <: WFF]
  : |-[(P <-> Q) -> (P -> Q)]
  = Placeholder()

  def BiInf [P <: WFF, Q <: WFF]
  (_1: |-[P -> Q], _2: |-[Q -> P])
  : |-[ P <-> Q ]
  = {
    val _3: |-[P -> (Q -> P)] = Simp()
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
  = Placeholder()

  def BiTransi [P <: WFF, Q <: WFF, R <: WFF]
  (_1: |-[P <-> Q], _2: |-[Q <-> R])
  : |-[ P <-> R ]
  = Placeholder()
}

/**
  * Introduce logical conjunction and disjunction
  */
object Junction {
  import Axioms._
  import Implication._
  import Negation._
  import Equivalence._

  @showAsInfix
  trait &   [L <: WFF, R <: WFF] extends WFF
  @showAsInfix
  trait |   [L <: WFF, R <: WFF] extends WFF

  object DfOr extends Axiom {
    def apply[P <: WFF, Q <: WFF]()
    : |-[(P | Q) <-> (~[P] -> Q)]
    = ax()
  }

  def OrComm [P <: WFF, Q <: WFF]
  : |-[ (P | Q) <-> (Q | P) ]
  = {
    val _1: |-[ (P | Q) <-> (~[P] -> Q) ] = DfOr()
    Placeholder()
  }
}

object Truth {
  import Axioms._

  trait T extends WFF
  trait F extends WFF
}