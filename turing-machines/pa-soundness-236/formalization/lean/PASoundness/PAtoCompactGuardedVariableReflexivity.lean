import PASoundness.PAtoCompactCandidateReflexiveObject
import PASoundness.PAtoCompactAlphaMapOne

/-! Capture-safe single bound-name moves for the fixed candidate-reflexivity
source. Full template alignment and the guarded variable leaf remain open. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactGuardedVariableReflexivity

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactCandidateReflexivity
open PASoundness.PAtoCompactCandidateReflexiveObject
open PASoundness.PAtoCompactDiagonalReflexiveMatrixTransport
open PASoundness.PAtoCompactAlphaMapOne

theorem source_binders : sourceBody.binders =
    {0,2,3,4,5,6,19,20,21,22,31,32,34,35,37,38,41} := by decide

theorem source_no_shadow :
    ∀ x ∈ sourceBody.binders, NoShadow x sourceBody := by
  rw [source_binders]
  decide

theorem source_free : sourceBody.free = {30} := by decide

/-- Any one of the fixed source's bound-name labels can be moved to an unused
name, with literal K derivations in both directions. This may move several
disjoint binders sharing the label; it is one name change only. -/
def source_binder_alpha (x y : Nat) (hx : x ∈ sourceBody.binders)
    (hy : y ∉ sourceBody.names) : ProofEquiv sourceBody (mapNames (rename x y) sourceBody) := by
  have hxy : x ≠ y := by
    intro h
    subst y
    exact hy (sourceBody.binders_subset_names hx)
  have hfree : x ∉ sourceBody.free := by
    rw [source_free]
    intro h
    have he : x = 30 := Finset.mem_singleton.mp h
    subst x
    rw [source_binders] at hx
    norm_num at hx
  exact alpha_map_one x y sourceBody hxy hfree hy (source_no_shadow x hx)

/-- The established candidate-reflexivity proof remains valid after any one
such capture-safe move. -/
def source_reflexivity_alpha (x y : Nat) (hx : x ∈ sourceBody.binders)
    (hy : y ∉ sourceBody.names) :
    KDerivation (mapNames (rename x y) sourceBody).encode :=
  .mp candidate_reflexive (source_binder_alpha x y hx hy).forward

end PASoundness.PAtoCompactGuardedVariableReflexivity

#print axioms PASoundness.PAtoCompactGuardedVariableReflexivity.source_binder_alpha
#print axioms PASoundness.PAtoCompactGuardedVariableReflexivity.source_reflexivity_alpha
