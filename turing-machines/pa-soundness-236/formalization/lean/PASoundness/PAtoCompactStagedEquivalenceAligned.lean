import PASoundness.PAtoCompactStagedEquivalenceAlpha
import PASoundness.PAtoCompactVacuousEqualityAlignment

/-! Align the staged allocated equivalence with independent source and target
labels when the target does not collide with the temporary staging name. -/
namespace PASoundness.PAtoCompactStagedEquivalenceAligned

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactStagedEquivalenceAlpha PASoundness.PAtoCompactVacuousEqualityAlignment

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The target name must not be 25: otherwise the final replacement would
also rename the target installed at the preceding step. -/
theorem allocated_shape (x y : Nat) (hy25 : y ≠ 25) :
    allocatedStaged x y = equivAt 100 x y := by
  have h0 : replace 0 25 (equivAt 100 0 1) = equivAt 100 25 1 := by
    simpa [rename] using equivAt_replace 100 0 1 0 25 (by decide)
  have h1 : replace 1 y (equivAt 100 25 1) = equivAt 100 25 y := by
    simpa [rename] using equivAt_replace 100 25 1 1 y (by decide)
  have h2 : replace 25 x (equivAt 100 25 y) = equivAt 100 x y := by
    simpa [rename,hy25] using equivAt_replace 100 25 y 25 x (by decide)
  unfold allocatedStaged
  rw [h0,h1,h2]

def staged_to_allocated (x y : Nat) (hx : x < 102) (hy : y < 102)
    (hxraw : x ∉ equivalentFormula.binders) (hyraw : y ∉ equivalentFormula.binders) (hy25 : y ≠ 25) :
    KDerivation (imp (rawStaged x y).encode (equivAt 100 x y).encode) := by
  simpa only [allocated_shape x y hy25] using staged_forward x y hx hy hxraw hyraw

def allocated_to_staged (x y : Nat) (hx : x < 102) (hy : y < 102)
    (hxraw : x ∉ equivalentFormula.binders) (hyraw : y ∉ equivalentFormula.binders) (hy25 : y ≠ 25) :
    KDerivation (imp (equivAt 100 x y).encode (rawStaged x y).encode) := by
  simpa only [allocated_shape x y hy25] using staged_backward x y hx hy hxraw hyraw

end PASoundness.PAtoCompactStagedEquivalenceAligned

#print axioms PASoundness.PAtoCompactStagedEquivalenceAligned.allocated_shape
#print axioms PASoundness.PAtoCompactStagedEquivalenceAligned.staged_to_allocated
#print axioms PASoundness.PAtoCompactStagedEquivalenceAligned.allocated_to_staged
