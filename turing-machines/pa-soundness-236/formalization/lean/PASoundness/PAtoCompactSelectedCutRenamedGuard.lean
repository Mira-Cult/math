import PASoundness.PAtoCompactSelectedCutGraphAlias
import PASoundness.PAtoCompactLessRightSegmentAliases
import PASoundness.PAtoCompactScopedActiveReplace

/-! Capture-safe relabeling of selected proper-cut transport. Whole-formula
freshening occurs before changing the free names; the target cut and the
canonical quotient aliases are bound at distinct names. No suffix isomorphism
or output-transport theorem is claimed. -/
namespace PASoundness.PAtoCompactSelectedCutRenamedGuard
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactLessRightSegmentAliases
open PASoundness.PAtoCompactLessRightSegmentTransport PASoundness.PAtoCompactSelectedCutGraphAlias
open PASoundness.PAtoCompactEquivalentAliasInstantiation PASoundness.PAtoCompactEquivalentAliasGuardLift
open PASoundness.PAtoCompactScopedActiveReplace
set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The exact original selected-cut theorem as a named implication frame. -/
def sourceFrame : Formula := .imp (namedTrans 0 11 12)
  (.imp (namedTrans 1 16 18) (.imp (.member 0 2)
    (.imp orderFormula (.imp bijectionFormula selectedAlias))))

def targetOrder : Formula := replace 6 60 (replace 1 8 (replace 0 32 orderFormula))
def targetBijection : Formula := replace 6 60 (replace 1 8 (replace 0 32 bijectionFormula))
/-- Alias binders are moved away from 41 before that name is used as the
new target-cut witness. -/
def shiftedAliases : Formula := replace 41 71 (replace 40 70 originalAliases)
def shiftedGuard : Formula := .ex 70 (namedBoth (.equal 70 33)
  (.ex 71 (namedBoth (.equal 71 41) shiftedAliases)))
def targetBody : Formula := namedBoth (namedBoth (.member 8 41) (graphFormula 60 33 41)) shiftedGuard
def targetSelected : Formula := .ex 41 targetBody
def targetFrame : Formula := .imp (namedTrans 32 11 12)
  (.imp (namedTrans 8 16 18) (.imp (.member 32 33)
    (.imp targetOrder (.imp targetBijection targetSelected))))

private theorem source_names_lt : ∀ v ∈ sourceFrame.names, v < 100 := by decide
private theorem target_names_lt : ∀ v ∈ targetFrame.names, v < 100 := by decide
private def freshSource := freshen sourceFrame 100 source_names_lt
private def freshTarget := freshen targetFrame 100 target_names_lt

/-- Alpha-standardization also moves the selected witness 5→41 and the
endpoint aliases 40/41→70/71, without substituting through their binders. -/
private theorem frame_shape :
    replace 6 60 (replace 2 33 (replace 1 8 (replace 0 32 freshSource.formula))) =
      freshTarget.formula := by decide

/-- Finite K transport of the supplied proper-cut theorem to fixed labels.
The same graph60 edge and target cut41 are retained under the shifted alias
guard. Every displayed transitivity and source-matrix premise remains. -/
def selected_cut_renamed_guard : KDerivation targetFrame.encode := by
  have hsource : KDerivation sourceFrame.encode := by
    simpa only [sourceFrame,namedTrans,sourceTrans,targetTrans,sourceMember,
      transitiveCode,transitiveBody,Formula.encode] using selected_cut_graph_alias
  have hf : KDerivation freshSource.formula.encode := .mp hsource freshSource.equivalent.forward
  have h32 := replace_derivation 0 32 freshSource.formula (by decide) (by decide) hf
  have h8 := replace_derivation 1 8 (replace 0 32 freshSource.formula) (by decide) (by decide) h32
  have h33 := replace_derivation 2 33 (replace 1 8 (replace 0 32 freshSource.formula))
    (by decide) (by decide) h8
  have h60 := replace_derivation 6 60 (replace 2 33 (replace 1 8 (replace 0 32 freshSource.formula)))
    (by decide) (by decide) h33
  rw [frame_shape] at h60
  exact .mp h60 freshTarget.equivalent.backward

theorem selected_cut_renamed_guard_certificate : theoremCode (certificate selected_cut_renamed_guard) =
    targetFrame.encode := certificate_correct selected_cut_renamed_guard
end PASoundness.PAtoCompactSelectedCutRenamedGuard

#print axioms PASoundness.PAtoCompactSelectedCutRenamedGuard.selected_cut_renamed_guard
#print axioms PASoundness.PAtoCompactSelectedCutRenamedGuard.selected_cut_renamed_guard_certificate
