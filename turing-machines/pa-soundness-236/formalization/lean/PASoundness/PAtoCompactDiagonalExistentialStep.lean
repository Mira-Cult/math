import PASoundness.PAtoCompactDiagonalInvariantStep
import PASoundness.PAtoCompactDiagonalAdjoinElim
import PASoundness.PAtoCompactDiagonalPairSpecialize

/-! Eliminate the supplied new diagonal graph and pair witnesses in one K
successor step. This does not establish induction, identity-graph totality,
or a collection principle. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDiagonalExistentialStep
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactDiagonalInvariantStep
open PASoundness.PAtoCompactDiagonalNoGarbageStep PASoundness.PAtoCompactDiagonalNoGarbageAll

/-- Named version of the two displayed diagonal graph invariant clauses. -/
def invariantNamed (k g : Nat) : Formula :=
  namedBoth (.all 2 (.imp (.member k 2) (graphFormula g 2 2)))
    (.all 9 (.imp (.member g 9)
      (.ex 3 (namedBoth (.member k 3) (pairFormula 9 3 3)))))

/-- The named invariant is the literal invariant used in the checked step. -/
theorem old_invariant_encode : (invariantNamed 0 6).encode = oldInvariant := by
  rfl

theorem new_invariant_encode : (invariantNamed 1 7).encode = newInvariant := by
  rfl

/-- Rebind the constructed graph under an existential using a fresh label 11. -/
def invariant_intro : KDerivation
    (imp newInvariant (existsCode 11 (invariantNamed 1 11).encode)) := by
  let f := invariantNamed 1 11
  have h := exists_variable_intro 11 7 f (by decide) (by decide) (by decide)
  have hf : CompactNamed.replace 11 7 f = invariantNamed 1 7 := by decide
  rw [hf, new_invariant_encode] at h
  exact h

/-- Eliminate an explicitly supplied existential adjunction witness; the
point-pair witness remains a displayed antecedent. -/
def eliminate_adjoin
    (hA : KDerivation (existsCode 7 (adjoinCode 6 8 7 19))) : KDerivation
    (imp (successorCode 0 1 2) (imp (pairFormula 8 0 0).encode
      (imp oldInvariant (existsCode 11 (invariantNamed 1 11).encode)))) := by
  let S := successorCode 0 1 2
  let A := adjoinCode 6 8 7 19
  let P := (pairFormula 8 0 0).encode
  let O := oldInvariant
  let E := existsCode 11 (invariantNamed 1 11).encode
  let G := imp S (imp P (imp O E))
  let fGoal : Formula := .imp (namedSuccessor 0 1 2)
    (.imp (pairFormula 8 0 0) (.imp (invariantNamed 0 6) (.ex 11 (invariantNamed 1 11))))
  have hfresh : 7 ∉ fGoal.names := by decide
  have hv : KDerivation (imp G (allCode 7 G)) := by
    have h := fGoal.vacuity 7 hfresh
    simpa [fGoal, G, S, P, O, E, namedSuccessor, namedSuccessorBody, namedBoth, namedEither,
      successorCode, old_invariant_encode, Formula.encode, CompactProof.both,
      CompactProof.neg, CompactDerivations.either] using h
  have hlocal : KDerivation (imp A G) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Γ := [O,P,S,A]
    have hs : Context Γ S := .hypothesis (by simp [Γ])
    have hp : Context Γ P := .hypothesis (by simp [Γ])
    have ho : Context Γ O := .hypothesis (by simp [Γ])
    have ha : Context Γ A := .hypothesis (by simp [Γ])
    have hn : Context Γ newInvariant := .mp ho (.mp hp (.mp ha (.mp hs (.closed diagonal_invariant_step))))
    exact .mp hn (.closed invariant_intro)
  apply Context.closeEmpty
  exact Context.existsElim hv (.closed (.generalize 7 hlocal)) (.closed hA)

/-- Eliminate both explicitly supplied existential witnesses. -/
def eliminate_pair_and_adjoin
    (hA : KDerivation (existsCode 7 (adjoinCode 6 8 7 19)))
    (hP : KDerivation (existsCode 8 (pairFormula 8 0 0).encode)) : KDerivation
    (imp (successorCode 0 1 2)
      (imp oldInvariant (existsCode 11 (invariantNamed 1 11).encode))) := by
  let S := successorCode 0 1 2
  let P := (pairFormula 8 0 0).encode
  let O := oldInvariant
  let E := existsCode 11 (invariantNamed 1 11).encode
  let F := imp S (imp O E)
  let fGoal : Formula := .imp (namedSuccessor 0 1 2)
    (.imp (invariantNamed 0 6) (.ex 11 (invariantNamed 1 11)))
  have hfresh : 8 ∉ fGoal.names := by decide
  have hv : KDerivation (imp F (allCode 8 F)) := by
    have h := fGoal.vacuity 8 hfresh
    simpa [fGoal, F, S, O, E, namedSuccessor, namedSuccessorBody, namedBoth, namedEither,
      successorCode, old_invariant_encode, Formula.encode, CompactProof.both,
      CompactProof.neg, CompactDerivations.either] using h
  have hlocal : KDerivation (imp P F) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Γ := [O,S,P]
    have hs : Context Γ S := .hypothesis (by simp [Γ])
    have hp : Context Γ P := .hypothesis (by simp [Γ])
    have ho : Context Γ O := .hypothesis (by simp [Γ])
    exact .mp ho (.mp hp (.mp hs (.closed (eliminate_adjoin hA))))
  apply Context.closeEmpty
  exact Context.existsElim hv (.closed (.generalize 8 hlocal)) (.closed hP)

/-- From a supplied successor and old diagonal invariant, K constructs a new
graph satisfying the diagonal coverage and no-garbage invariant. -/
def diagonal_successor_exists : KDerivation
    (imp (successorCode 0 1 2)
      (imp oldInvariant (existsCode 11 (invariantNamed 1 11).encode))) :=
  eliminate_pair_and_adjoin PAtoCompactDiagonalAdjoinElim.fixed_adjoin_exists
    PAtoCompactDiagonalPairSpecialize.diagonal_pair_exists

theorem diagonal_successor_exists_certificate :
    theoremCode (certificate diagonal_successor_exists) =
      imp (successorCode 0 1 2)
        (imp oldInvariant (existsCode 11 (invariantNamed 1 11).encode)) :=
  certificate_correct diagonal_successor_exists

end PASoundness.PAtoCompactDiagonalExistentialStep

#print axioms PASoundness.PAtoCompactDiagonalExistentialStep.invariant_intro
#print axioms PASoundness.PAtoCompactDiagonalExistentialStep.eliminate_pair_and_adjoin
#print axioms PASoundness.PAtoCompactDiagonalExistentialStep.diagonal_successor_exists
#print axioms PASoundness.PAtoCompactDiagonalExistentialStep.diagonal_successor_exists_certificate
