import PASoundness.PAtoCompactDiagonalExistentialStep
import PASoundness.PAtoCompactOrderIsoZero
import PASoundness.PAtoCompactZeroExistence

/-! A zero input has a represented diagonal graph in K. The input zero graph
is an explicit hypothesis, and a separate zero graph is constructed for its
diagonal relation. No general graph totality or induction is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDiagonalInvariantBase
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactZeroExistence
open PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactOrderIsoZero
open PASoundness.PAtoCompactDiagonalNoGarbageStep PASoundness.PAtoCompactDiagonalNoGarbageAll
open PASoundness.PAtoCompactDiagonalInvariantStep PASoundness.PAtoCompactDiagonalExistentialStep

/-- An empty graph witness with graph name 6 and test name 13. -/
def empty_graph_exists : KDerivation (existsCode 6 (zeroCode 6 13)) := by
  let f : Formula := .all 13 (.imp (.member 1 13) .bottom)
  have ha := (CompactNamed.existentialAlpha 1 6 f (by decide) (by decide) (by decide)).1
  have he : (CompactNamed.replace 1 6 f).encode = zeroCode 6 13 := by
    simp [f, zeroCode, CompactNamed.replace, CompactNamed.rename, Formula.encode,
      CompactProof.neg]
  have hf : f.encode = zeroCode 1 13 := by rfl
  rw [hf,he] at ha
  exact .mp (zero_graph_exists 13 (by decide)) ha

/-- Empty input and empty graph jointly satisfy both old invariant clauses. -/
def empty_input_invariant : KDerivation
    (imp (zeroCode 0 12) (imp (zeroCode 6 13) oldInvariant)) := by
  let Z := zeroCode 0 12
  let G := zeroCode 6 13
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [G,Z]
  have hz : Context Γ Z := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have hc : Context Γ oldCoverage :=
    .mp hz (.closed (zero_guard_all 0 12 2 (graphFormula 6 2 2).encode
      (by decide) (by decide) (by decide)))
  have hn : Context Γ oldNoGarbage :=
    .mp hg (.closed (zero_guard_all 6 13 9 oldEntry
      (by decide) (by decide) (by decide)))
  exact Context.conjunctionIntro hc hn

/-- A concrete old graph witness can be introduced at fresh binder 11. -/
def old_invariant_intro : KDerivation
    (imp oldInvariant (existsCode 11 (invariantNamed 0 11).encode)) := by
  let f := invariantNamed 0 11
  have h := exists_variable_intro 11 6 f (by decide) (by decide) (by decide)
  have hf : CompactNamed.replace 11 6 f = invariantNamed 0 6 := by decide
  rw [hf, old_invariant_encode] at h
  exact h

/-- From the supplied zero graph for the input, K constructs a graph with the
full diagonal coverage and no-garbage invariant. -/
def zero_diagonal_exists : KDerivation
    (imp (zeroCode 0 12) (existsCode 11 (invariantNamed 0 11).encode)) := by
  let Z := zeroCode 0 12
  let G := zeroCode 6 13
  let E := existsCode 11 (invariantNamed 0 11).encode
  let T := imp Z E
  let fGoal : Formula := .imp (.all 12 (.imp (.member 0 12) .bottom))
    (.ex 11 (invariantNamed 0 11))
  have hfresh : 6 ∉ fGoal.names := by decide
  have hv : KDerivation (imp T (allCode 6 T)) := by
    have h := fGoal.vacuity 6 hfresh
    simpa [fGoal,T,Z,E,zeroCode,Formula.encode,CompactProof.neg] using h
  have hlocal : KDerivation (imp G T) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [Z,G]
    have hz : Context Γ Z := .hypothesis (by simp [Γ])
    have hg : Context Γ G := .hypothesis (by simp [Γ])
    have hi : Context Γ oldInvariant := .mp hg (.mp hz (.closed empty_input_invariant))
    exact .mp hi (.closed old_invariant_intro)
  apply Context.closeEmpty
  exact Context.existsElim hv (.closed (.generalize 6 hlocal)) (.closed empty_graph_exists)

theorem zero_diagonal_exists_certificate :
    theoremCode (certificate zero_diagonal_exists) =
      imp (zeroCode 0 12) (existsCode 11 (invariantNamed 0 11).encode) :=
  certificate_correct zero_diagonal_exists

end PASoundness.PAtoCompactDiagonalInvariantBase

#print axioms PASoundness.PAtoCompactDiagonalInvariantBase.zero_diagonal_exists
#print axioms PASoundness.PAtoCompactDiagonalInvariantBase.zero_diagonal_exists_certificate
