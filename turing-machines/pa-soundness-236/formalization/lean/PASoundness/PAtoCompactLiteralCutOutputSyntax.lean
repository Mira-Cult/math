import PASoundness.PAtoCompactLiteralCutBaseSyntax
import PASoundness.PAtoCompactAddTermBody

/-! Free-name, binder and replacement facts for output alpha conversion of
allocated literal-cut addition. These are syntactic facts, not existence or
soundness results. The input labels may coincide. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLiteralCutOutputSyntax
open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactLiteralCutAdditionDefinition
open PASoundness.PAtoCompactLiteralCutBaseSyntax
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactAlphaMapOne
open PASoundness.PAtoCompactGuardElimination PASoundness.PAtoCompactScopedAlphaInvariant

private theorem unbound30 : 30 ∉ (normalizeBottom literalCut).binders := by decide
private theorem unbound31 : 31 ∉ (normalizeBottom literalCut).binders := by decide
private theorem unbound32 : 32 ∉ (normalizeBottom literalCut).binders := by decide
private theorem bounded : (normalizeBottom literalCut).names ⊆ Finset.range 38 := by decide
private theorem free : (normalizeBottom literalCut).free ⊆ ({30,31,32} : Finset Nat) := by decide

/-- Every binder belongs to the allocator's private block. -/
theorem literalCutAt_private (base x y z w : Nat) (h : w ∈ (literalCutAt base x y z).binders) :
    base + 2 ≤ w ∧ w < base + 64 := by
  unfold literalCutAt at h
  exact threeMap_private _ base 30 31 32 x y z unbound30 unbound31 unbound32
    (by intro v hv; have hv' := bounded hv; simp only [Finset.mem_range] at hv' ⊢; omega) w h

/-- No new free names are created by allocation. -/
theorem literalCutAt_free (base x y z : Nat) : (literalCutAt base x y z).free ⊆ {x,y,z} := by
  unfold literalCutAt
  refine (mapNames_free_subset _ _).trans ?_
  apply Finset.image_subset_iff.mpr
  intro a ha
  have h := free ha
  have : a = 30 ∨ a = 31 ∨ a = 32 := by simpa using h
  rcases this with rfl | rfl | rfl <;> simp [threeMap]

theorem below_not_binder (base x y z q : Nat) (hq : q < base + 2) :
    q ∉ (literalCutAt base x y z).binders := by
  intro h
  have hh := literalCutAt_private base x y z q h
  omega

/-- Replacement below the private block acts on the three parameters only;
the target's binder-capture condition must be checked separately. -/
theorem replace_literalCutAt (base a b out x y : Nat) (hx : x < base + 2) :
    replace x y (literalCutAt base a b out) =
      literalCutAt base (rename x y a) (rename x y b) (rename x y out) := by
  rw [← map_eq_replace x y (literalCutAt base a b out) (below_not_binder base a b out x hx)]
  unfold literalCutAt
  rw [mapNames_compose]
  congr 1
  funext z
  by_cases h0 : z = 30
  · simp [threeMap, h0]
  · by_cases h1 : z = 31
    · simp [threeMap, h1]
    · by_cases h2 : z = 32
      · simp [threeMap, h2]
      · have hne : base + 2 + z ≠ x := by omega
        simp [threeMap, h0, h1, h2, rename, hne]
end PASoundness.PAtoCompactLiteralCutOutputSyntax
#print axioms PASoundness.PAtoCompactLiteralCutOutputSyntax.literalCutAt_private
#print axioms PASoundness.PAtoCompactLiteralCutOutputSyntax.literalCutAt_free
#print axioms PASoundness.PAtoCompactLiteralCutOutputSyntax.below_not_binder
#print axioms PASoundness.PAtoCompactLiteralCutOutputSyntax.replace_literalCutAt
