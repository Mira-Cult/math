import PASoundness.PAtoCompactUnaryGraphFunctional
import PASoundness.PAtoCompactScopedActiveReplace

/-! Finite K alpha transport between safely staged literal equivalence and
the corresponding safely staged allocated equivalence. Keeping the staged
formula explicit avoids collapsing source and target names during replacement. -/
namespace PASoundness.PAtoCompactStagedEquivalenceAlpha

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactUnaryGraphFunctional PASoundness.PAtoCompactEquivNoShadow
open PASoundness.PAtoCompactTermGraphBinderRange PASoundness.PAtoCompactScopedActiveReplace

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def rawStaged (x y : Nat) : Formula := replace 25 x (replace 1 y (replace 0 25 equivalentFormula))
def allocatedStaged (x y : Nat) : Formula := replace 25 x (replace 1 y (replace 0 25 (equivAt 100 0 1)))

private def forwardFrame : Formula := .imp equivalentFormula (equivAt 100 0 1)
private def backwardFrame : Formula := .imp (equivAt 100 0 1) equivalentFormula

private theorem frames_not_binder (q : Nat) (hq : q < 102) (hr : q ∉ equivalentFormula.binders) :
    q ∉ forwardFrame.binders ∧ q ∉ backwardFrame.binders := by
  have he : q ∉ (equivAt 100 0 1).binders := by
    intro h
    have hp := equivAt_private 100 0 1 q h
    omega
  simpa only [forwardFrame,backwardFrame,Formula.binders,Finset.mem_union,not_or] using
    And.intro (And.intro hr he) (And.intro he hr)

private def stage (f : Formula) (x y : Nat)
    (h0 : 0 ∉ f.binders) (h1 : 1 ∉ f.binders) (h25 : 25 ∉ f.binders)
    (hx : x ∉ f.binders) (hy : y ∉ f.binders) (h : KDerivation f.encode) :
    KDerivation (replace 25 x (replace 1 y (replace 0 25 f))).encode := by
  have h0' := replace_derivation 0 25 f h0 h25 h
  have h1' := replace_derivation 1 y (replace 0 25 f)
    (by simpa only [replace_binders] using h1) (by simpa only [replace_binders] using hy) h0'
  exact replace_derivation 25 x (replace 1 y (replace 0 25 f))
    (by simpa only [replace_binders] using h25) (by simpa only [replace_binders] using hx) h1'

/-- The literal staged relation implies the allocated staged relation by K
proof data, with explicit bounds and raw-binder noncapture assumptions. -/
def staged_forward (x y : Nat) (hx : x < 102) (hy : y < 102)
    (hxraw : x ∉ equivalentFormula.binders) (hyraw : y ∉ equivalentFormula.binders) :
    KDerivation (imp (rawStaged x y).encode (allocatedStaged x y).encode) := by
  have hbase : KDerivation forwardFrame.encode := by
    simpa [forwardFrame,Formula.encode,equivTemplate,normalizeBottom_encode] using (canonical_equiv_alpha 100 (by omega)).forward
  have h := stage forwardFrame x y (frames_not_binder 0 (by decide) (by decide)).1
    (frames_not_binder 1 (by decide) (by decide)).1 (frames_not_binder 25 (by decide) (by decide)).1
    (frames_not_binder x hx hxraw).1 (frames_not_binder y hy hyraw).1 hbase
  change KDerivation (imp (rawStaged x y).encode (allocatedStaged x y).encode) at h
  exact h

/-- The reverse alpha transport preserves the same staged endpoints. -/
def staged_backward (x y : Nat) (hx : x < 102) (hy : y < 102)
    (hxraw : x ∉ equivalentFormula.binders) (hyraw : y ∉ equivalentFormula.binders) :
    KDerivation (imp (allocatedStaged x y).encode (rawStaged x y).encode) := by
  have hbase : KDerivation backwardFrame.encode := by
    simpa [backwardFrame,Formula.encode,equivTemplate,normalizeBottom_encode] using (canonical_equiv_alpha 100 (by omega)).backward
  have h := stage backwardFrame x y (frames_not_binder 0 (by decide) (by decide)).2
    (frames_not_binder 1 (by decide) (by decide)).2 (frames_not_binder 25 (by decide) (by decide)).2
    (frames_not_binder x hx hxraw).2 (frames_not_binder y hy hyraw).2 hbase
  change KDerivation (imp (allocatedStaged x y).encode (rawStaged x y).encode) at h
  exact h

end PASoundness.PAtoCompactStagedEquivalenceAlpha

#print axioms PASoundness.PAtoCompactStagedEquivalenceAlpha.rawStaged
#print axioms PASoundness.PAtoCompactStagedEquivalenceAlpha.allocatedStaged
#print axioms PASoundness.PAtoCompactStagedEquivalenceAlpha.staged_forward
#print axioms PASoundness.PAtoCompactStagedEquivalenceAlpha.staged_backward
