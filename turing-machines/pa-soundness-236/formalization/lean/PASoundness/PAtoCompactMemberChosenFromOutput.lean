import PASoundness.PAtoCompactMemberChosenGuardClosed
import PASoundness.PAtoCompactMemberChosenGraphElim

/-! Reassemble the explicit proper-cut guard while retaining one original
whole-output graph until target cut/suffix selection is complete. -/
namespace PASoundness.PAtoCompactMemberChosenFromOutput
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactOrdinalAddition PASoundness.PAtoCompactLessRightSegmentAliases
open PASoundness.PAtoCompactSelectedCutRenamedGuard PASoundness.PAtoCompactSelectedCutOutputMatrix
open PASoundness.PAtoCompactMemberCutSelectedTarget PASoundness.PAtoCompactMemberChosenGraphElim
set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Outer transitivity, the actual proper source cut, and its actual suffix.
The original graph is introduced separately from output equivalence. -/
def outerGuard : Formula := namedBoth (namedTrans 32 11 12) (namedBoth (namedTrans 8 16 18)
  (namedBoth (.member 32 33) suffixFormula))

theorem outer_guard_names_60 : 60 ∉ outerGuard.names := by decide

theorem outer_guard_free_60 : 60 ∉ outerGuard.free := by
  intro h
  exact outer_guard_names_60 ((Formula.free_subset_names outerGuard) h)

/-- Under the actual retained graph matrix, both the cut and suffix steps use
that same graph; no new graph or cut is selected between them. -/
noncomputable def chosen_under_graph : KDerivation
    (imp outerGuard.encode (imp graphMatrix.encode chosen.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [graphMatrix.encode,outerGuard.encode]
  have hm : Context Γ graphMatrix.encode := .head _ _
  have hg : Context Γ outerGuard.encode := .hypothesis (by simp [Γ])
  have hb : Context Γ targetBijection.encode := Context.conjunctionLeft hm
  have ho : Context Γ targetOrder.encode := Context.conjunctionRight hm
  have hs : Context Γ (namedTrans 32 11 12).encode := Context.conjunctionLeft hg
  have ht := Context.conjunctionRight hg
  have htgt : Context Γ (namedTrans 8 16 18).encode := Context.conjunctionLeft ht
  have ht := Context.conjunctionRight ht
  have hcut : Context Γ (member 32 33) := Context.conjunctionLeft ht
  have hsuffix : Context Γ suffixFormula.encode := Context.conjunctionRight ht
  have hguard : Context Γ PAtoCompactMemberChosenGuardInputs.guard.encode := by
    have h := Context.conjunctionIntro hs (Context.conjunctionIntro htgt
      (Context.conjunctionIntro hcut (Context.conjunctionIntro hsuffix
        (Context.conjunctionIntro ho hb))))
    simpa only [PAtoCompactMemberChosenGuardInputs.guard,namedBoth,Formula.not,
      Formula.encode,both,neg] using h
  exact .mp hguard (.closed PAtoCompactMemberChosenGuardClosed.chosen_from_guard)

/-- A represented whole-output equivalence and the explicit outer guard
produce one target cut/suffix pair with the original-cut and suffix
isomorphisms. No source term graph or candidate guard is inferred here. -/
noncomputable def chosen_from_output : KDerivation
    (imp outerGuard.encode (imp (PASoundness.PAtoCompactTermTranslation.equivAt 100 32 8).encode chosen.encode)) :=
  chosen_from_output_graph outerGuard outer_guard_free_60 chosen_under_graph

theorem chosen_from_output_certificate : theoremCode (certificate chosen_from_output) =
    imp outerGuard.encode (imp (PASoundness.PAtoCompactTermTranslation.equivAt 100 32 8).encode chosen.encode) := certificate_correct chosen_from_output
end PASoundness.PAtoCompactMemberChosenFromOutput

#print axioms PASoundness.PAtoCompactMemberChosenFromOutput.chosen_under_graph
#print axioms PASoundness.PAtoCompactMemberChosenFromOutput.chosen_from_output
#print axioms PASoundness.PAtoCompactMemberChosenFromOutput.chosen_from_output_certificate
