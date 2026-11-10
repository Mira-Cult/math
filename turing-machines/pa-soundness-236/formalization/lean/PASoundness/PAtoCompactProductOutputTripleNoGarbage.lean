import PASoundness.PAtoCompactProductOutputTripleCoordinateSplit
import PASoundness.PAtoCompactProductOutputTripleExtension
import PASoundness.PAtoCompactSuccGraphOutputLift

/-! Lift the pointwise edge split through the actual nested triple witness.
Every queried triple of the adjoined graph is an old triple or has the three
selected coordinates. This is one direction of the partial graph invariant. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputTripleNoGarbage

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactMultiplicationSingleTripleExtension
open PASoundness.PAtoCompactProductOutputTripleCoordinateSplit PASoundness.PAtoCompactSuccGraphOutputLift

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def guard : Formula := namedBoth (namedAdjoin 58 12 9 16)
  (namedBoth (pairFormula 12 11 33) (pairFormula 11 30 31))
def bodyAt (g a : Nat) : Formula := namedBoth (pairFormula a 56 57) (graphFormula g a 60)
def equalities : Formula := namedBoth (.equal 56 30)
  (namedBoth (.equal 57 31) (.equal 60 33))
def result : Formula := namedEither (tripleAt 58 56 57 60) equalities

theorem queried_triple_shape : tripleAt 9 56 57 60 = .ex 18 (bodyAt 9 18) := by decide
theorem old_triple_shape : tripleAt 58 56 57 60 = .ex 18 (bodyAt 58 18) := by decide
theorem new_body_shape : replace 18 55 (bodyAt 9 18) = bodyAt 9 55 := by decide
theorem old_body_shape : replace 18 55 (bodyAt 58 18) = bodyAt 58 55 := by decide

/-- Under the actual adjunction and the two selected pair descriptions, a
new triple is old or agrees with the selected triple in all three positions. -/
def triple_no_garbage : KDerivation (imp guard.encode
    (imp (tripleAt 9 56 57 60).encode result.encode)) := by
  have hn := (existentialAlpha 18 55 (bodyAt 9 18) (by decide) (by decide) (by decide)).1
  have ho := (existentialAlpha 18 55 (bodyAt 58 18) (by decide) (by decide) (by decide)).2
  rw [new_body_shape] at hn
  rw [old_body_shape] at ho
  have hp : KDerivation (imp guard.encode (imp (bodyAt 9 55).encode result.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [(bodyAt 9 55).encode,guard.encode]
    have hb : Context Γ (bodyAt 9 55).encode := .head _ _
    have hh : Context Γ guard.encode := .hypothesis (by simp [Γ])
    have hb' : Context Γ (both (pairFormula 55 56 57).encode (graphFormula 9 55 60).encode) := by
      simpa [bodyAt, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hb
    have hh' : Context Γ (both (adjoinCode 58 12 9 16) (both (pairFormula 12 11 33).encode
        (pairFormula 11 30 31).encode)) := by
      simpa [guard, namedAdjoin, namedBoth, namedEither, CompactNamed.Formula.not,
        CompactNamed.Formula.encode, adjoinCode, both, neg, either] using hh
    have hsplit := Context.mp (Context.conjunctionRight hb')
      (Context.mp (Context.conjunctionLeft hb')
        (Context.mp (Context.conjunctionRight (Context.conjunctionRight hh'))
          (Context.mp (Context.conjunctionLeft (Context.conjunctionRight hh'))
            (Context.mp (Context.conjunctionLeft hh') (.closed triple_coordinate_split)))))
    apply Context.disjunctionElim hsplit
    · let Δ := (graphFormula 58 55 60).encode :: Γ
      have hold : Context Δ (graphFormula 58 55 60).encode := .head _ _
      have hpair : Context Δ (pairFormula 55 56 57).encode := .under (Context.conjunctionLeft hb') _
      have hbody : Context Δ (bodyAt 58 55).encode := by
        simpa [bodyAt, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using
          Context.conjunctionIntro hpair hold
      have hi := existsIntroduce 55 (bodyAt 58 55) (by decide)
      have hsome : Context Δ (existsCode 55 (bodyAt 58 55).encode) := .mp hbody (.closed hi)
      have horiginal : Context Δ (tripleAt 58 56 57 60).encode := by
        simpa [old_triple_shape, CompactNamed.Formula.encode] using Context.mp hsome (.closed ho)
      simpa [result, equalities, namedEither, namedBoth, CompactNamed.Formula.not,
        CompactNamed.Formula.encode, either, both, neg] using Context.disjunctionLeft (b := equalities.encode) horiginal
    · let Δ := both (equal 56 30) (both (equal 57 31) (equal 60 33)) :: Γ
      have he0 : Context Δ (both (equal 56 30) (both (equal 57 31) (equal 60 33))) := .head _ _
      have he : Context Δ equalities.encode := by
        simpa [equalities, namedBoth, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using he0
      simpa [result, namedEither, CompactNamed.Formula.not, CompactNamed.Formula.encode, either, neg] using
        Context.disjunctionRight (a := (tripleAt 58 56 57 60).encode) he
  have helim := guarded_exists_left 55 guard.encode (bodyAt 9 55).encode result.encode
    (guard.vacuity 55 (by decide)) (result.vacuity 55 (by decide)) hp
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(tripleAt 9 56 57 60).encode,guard.encode]
  have ht : Context Γ (tripleAt 9 56 57 60).encode := .head _ _
  have hg : Context Γ guard.encode := .hypothesis (by simp [Γ])
  have hs : Context Γ (existsCode 55 (bodyAt 9 55).encode) := by
    have hinput : Context Γ (existsCode 18 (bodyAt 9 18).encode) := by
      simpa [queried_triple_shape, CompactNamed.Formula.encode] using ht
    exact .mp hinput (.closed hn)
  exact .mp hs (.mp hg (.closed helim))

theorem triple_no_garbage_certificate : theoremCode (certificate triple_no_garbage) =
    imp guard.encode (imp (tripleAt 9 56 57 60).encode result.encode) := certificate_correct _

end PASoundness.PAtoCompactProductOutputTripleNoGarbage

#print axioms PASoundness.PAtoCompactProductOutputTripleNoGarbage.triple_no_garbage
#print axioms PASoundness.PAtoCompactProductOutputTripleNoGarbage.triple_no_garbage_certificate
