import PASoundness.PAtoCompactFixedFirstCoverageBase
import PASoundness.PAtoCompactFreeVacuity
import PASoundness.CompactQuantifiers

/-! Quantified K coverage for a fixed-first row across a successor prefix.
The old coverage and a top-point witness are explicit antecedents; no row
witness is constructed and no pair-representative uniqueness is assumed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactFixedFirstInsideCoverage
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactFixedFirstCoverageBase
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The exact coverage conclusion at the active row index 3. -/
def pointWitness : Formula := .ex 4 (.ex 5 (namedBoth (graphFormula 6 3 4)
  (namedBoth (pairFormula 5 30 3) (graphFormula 12 5 4))))

/-- The same witness condition at the new top prefix point 0. -/
def topWitness : Formula := replace 3 0 pointWitness
private def oldBody : Formula := .imp (namedBoth (.member 0 3) (.member 31 3)) pointWitness
private def newBody : Formula := .imp (namedBoth (.member 1 3) (.member 31 3)) pointWitness
private def S : Formula := namedSuccessor 0 1 2
private theorem old_shape : coverage 12 = .all 3 oldBody := rfl
private theorem new_shape : replace 0 1 (coverage 12) = .all 3 newBody := by decide

/-- Given old graph coverage and an explicit witness at the top point, the
same graph covers every point in the successor-prefix/domain intersection. -/
def inside_coverage : KDerivation (imp (successorCode 0 1 2)
    (imp (coverage 12).encode (imp topWitness.encode
      (replace 0 1 (coverage 12)).encode))) := by
  let f := namedSuccessorBody 0 1 2
  have hi := universalInstance 2 3 f (by decide) (by decide) (by decide)
  have hi' : KDerivation (imp (successorCode 0 1 2)
      (both (imp (member 1 3) (either (equal 3 0) (member 0 3)))
        (imp (either (equal 3 0) (member 0 3)) (member 1 3)))) := by
    simpa [f,namedSuccessorBody,namedBoth,namedEither,successorCode,
      Formula.encode,replace,rename,both,neg,either] using hi
  have heq : KDerivation (imp (equal 3 0) (imp topWitness.encode pointWitness.encode)) := by
    simpa [topWitness] using (equalityReplace 3 0 pointWitness (by decide) (by decide)).2
  have hold : KDerivation (imp (coverage 12).encode oldBody.encode) := by
    have h := allSpecialize 3 oldBody (by decide)
    simpa [old_shape,Formula.encode] using h
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [topWitness.encode,(coverage 12).encode,successorCode 0 1 2]
  have ht : Context Γ topWitness.encode := .head _ _
  have ho : Context Γ (coverage 12).encode := .hypothesis (by simp [Γ])
  have hs : Context Γ (successorCode 0 1 2) := .hypothesis (by simp [Γ])
  have hpoint : Context Γ newBody.encode := by
    apply Context.deduction
    let Δ := [both (member 1 3) (member 31 3),topWitness.encode,(coverage 12).encode,successorCode 0 1 2]
    have hm : Context Δ (both (member 1 3) (member 31 3)) := .head _ _
    have hc : Context Δ (either (equal 3 0) (member 0 3)) :=
      .mp (Context.conjunctionLeft hm)
        (Context.conjunctionLeft (.mp (.under hs _) (.closed hi')))
    change Context Δ pointWitness.encode
    apply Context.disjunctionElim hc
    · have he : Context (equal 3 0 :: Δ) (equal 3 0) := .head _ _
      exact .mp (.under (.under ht _) _) (.mp he (.closed heq))
    · have hm0 : Context (member 0 3 :: Δ) (member 0 3) := .head _ _
      have hy : Context (member 0 3 :: Δ) (member 31 3) := .under (Context.conjunctionRight hm) _
      have hp : Context (member 0 3 :: Δ) (imp (both (member 0 3) (member 31 3)) pointWitness.encode) := by
        have ho' : Context (member 0 3 :: Δ) (coverage 12).encode := .hypothesis (by simp [Δ])
        have h : Context (member 0 3 :: Δ) oldBody.encode := .mp ho' (.closed hold)
        simpa [oldBody,namedBoth,Formula.not,Formula.encode,both,neg] using h
      exact .mp (Context.conjunctionIntro hm0 hy) hp
  have hv : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 3 q)) := by
    intro q hq
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hq
    by_cases h : q = topWitness.encode
    · subst q; exact topWitness.vacuity 3 (by decide)
    by_cases h' : q = (coverage 12).encode
    · subst q; exact free_vacuity 3 (coverage 12) (by decide)
    · have he : q = successorCode 0 1 2 := by simpa [h,h'] using hq
      subst q
      have hs' := S.vacuity 3 (by decide)
      simpa [S,namedSuccessor,namedSuccessorBody,namedBoth,namedEither,Formula.encode,
        Formula.not,successorCode,both,neg,either] using hs'
  have hall := Context.generalize 3 hv hpoint
  simpa [new_shape,Formula.encode] using hall

theorem inside_coverage_certificate : theoremCode (certificate inside_coverage) =
    imp (successorCode 0 1 2) (imp (coverage 12).encode (imp topWitness.encode
      (replace 0 1 (coverage 12)).encode)) := certificate_correct inside_coverage
end PASoundness.PAtoCompactFixedFirstInsideCoverage
#print axioms PASoundness.PAtoCompactFixedFirstInsideCoverage.inside_coverage
#print axioms PASoundness.PAtoCompactFixedFirstInsideCoverage.inside_coverage_certificate
