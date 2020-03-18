package proofs.and.ladders

import proofs.and.ladders.logic.propositional.Axioms.->
import proofs.and.ladders.logic.propositional.Equivalence.<->
import proofs.and.ladders.logic.propositional.{Equivalence, Implication, Negation, WFF}

object Main {
  def main(args: Array[String]): Unit = {

    object P extends WFF
    type P = P.type
    object Q extends WFF
    type Q = Q.type

    val concl = Negation.TransRev[P, Q]

    println(concl)
    println(concl.axioms)
    println(concl.proofString)
  }
}
