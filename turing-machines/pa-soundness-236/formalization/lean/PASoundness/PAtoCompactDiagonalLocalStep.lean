import PASoundness.PAtoCompactDiagonalExistentialStep

/-! A witness-eliminated local K step for the diagonal-graph predicate. It
assumes a literal successor graph and an old existential invariant; this does
not establish the base, a global induction schema, graph collection, or a PA
interpretation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDiagonalLocalStep
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactDiagonalInvariantStep PASoundness.PAtoCompactDiagonalExistentialStep

/-- Rename the bound old graph from 11 to 6, avoiding all inner binders. -/
def old_graph_alpha : KDerivation
    (imp (existsCode 11 (invariantNamed 0 11).encode) (existsCode 6 oldInvariant)) := by
  let f := invariantNamed 0 11
  have h := (CompactNamed.existentialAlpha 11 6 f (by decide) (by decide) (by decide)).1
  have hr : CompactNamed.replace 11 6 f = invariantNamed 0 6 := by decide
  rw [hr, old_invariant_encode] at h
  exact h

/-- If a successor graph is supplied, an existential old diagonal-graph
invariant yields an existential new diagonal-graph invariant. -/
def local_successor_step : KDerivation
    (imp (successorCode 0 1 2)
      (imp (existsCode 11 (invariantNamed 0 11).encode)
        (existsCode 11 (invariantNamed 1 11).encode))) := by
  let S := successorCode 0 1 2
  let O := oldInvariant
  let F := existsCode 11 (invariantNamed 0 11).encode
  let E := existsCode 11 (invariantNamed 1 11).encode
  let T := imp S E
  let fT : Formula := .imp (namedSuccessor 0 1 2) (.ex 11 (invariantNamed 1 11))
  have hfresh : 6 ∉ fT.names := by decide
  have hv : KDerivation (imp T (allCode 6 T)) := by
    have h := fT.vacuity 6 hfresh
    simpa [fT,T,S,E,namedSuccessor,namedSuccessorBody,namedBoth,namedEither,
      successorCode,Formula.encode,CompactProof.both,CompactProof.neg,
      CompactDerivations.either] using h
  have hlocal : KDerivation (imp O T) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [S,O]
    have hs : Context Γ S := .hypothesis (by simp [Γ])
    have ho : Context Γ O := .hypothesis (by simp [Γ])
    exact .mp ho (.mp hs (.closed diagonal_successor_exists))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [F,S]
  have hf : Context Γ F := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hex : Context Γ (existsCode 6 O) := .mp hf (.closed old_graph_alpha)
  have ht : Context Γ T := Context.existsElim hv (.closed (.generalize 6 hlocal)) hex
  exact .mp hs ht

theorem local_successor_step_certificate :
    theoremCode (certificate local_successor_step) =
      imp (successorCode 0 1 2)
        (imp (existsCode 11 (invariantNamed 0 11).encode)
          (existsCode 11 (invariantNamed 1 11).encode)) :=
  certificate_correct local_successor_step

end PASoundness.PAtoCompactDiagonalLocalStep

#print axioms PASoundness.PAtoCompactDiagonalLocalStep.old_graph_alpha
#print axioms PASoundness.PAtoCompactDiagonalLocalStep.local_successor_step
#print axioms PASoundness.PAtoCompactDiagonalLocalStep.local_successor_step_certificate
