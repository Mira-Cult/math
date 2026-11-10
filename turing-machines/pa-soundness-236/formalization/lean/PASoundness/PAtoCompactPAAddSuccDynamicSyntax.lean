import PASoundness.PAtoCompactTemplateBlockShift
import PASoundness.PAtoCompactAdjunction
import PASoundness.PAtoCompactZeroSuccessor
import PASoundness.PAtoCompactTermGraphBinderRange

/-! Syntactic five-operand relabeling for an allocated addition successor
frame. This file does not assert a finite K derivation by itself. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPAAddSuccDynamicSyntax
open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactTemplateBlockShift PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTermGraphBinderRange

def sigma (x y z ys zs n : Nat) : Nat :=
  if n = 30 then x else if n = 31 then y else if n = 32 then z else
  if n = 38 then ys else if n = 45 then zs else n

def fixedFrame (b w : Nat) : Formula :=
  .imp (domainAt b 31) (.imp (domainAt b 32)
    (.imp (namedSuccessor 31 38 w) (.imp (namedSuccessor 32 45 w)
      (.imp (addAt b 30 31 32) (addAt b 30 38 45)))))

def assignedFrame (b w x y z ys zs : Nat) : Formula :=
  .imp (domainAt b y) (.imp (domainAt b z)
    (.imp (namedSuccessor y ys w) (.imp (namedSuccessor z zs w)
      (.imp (addAt b x y z) (addAt b x ys zs)))))

theorem sigma_block (x y z ys zs b : Nat) (hb : 45 < b) :
    ∀ i < 64, sigma x y z ys zs (b+i) = b+i := by
  intro i hi
  simp [sigma, show b+i ≠ 30 by omega, show b+i ≠ 31 by omega,
    show b+i ≠ 32 by omega, show b+i ≠ 38 by omega, show b+i ≠ 45 by omega]

/-- Names below the private template block are not bound in the fixed
frame unless they are the raw-successor test binder. -/
theorem outside_binders (b w k : Nat) (hk : k < b+2) (hkw : k ≠ w) :
    k ∉ (fixedFrame b w).binders := by
  intro h
  simp only [fixedFrame, Formula.binders, Finset.mem_union] at h
  rcases h with h | h | h | h | h | h
  · have hh := domainAt_private b 31 k h; omega
  · have hh := domainAt_private b 32 k h; omega
  · simp [namedSuccessor, namedSuccessorBody, namedBoth, namedEither, Formula.binders, hkw] at h
  · simp [namedSuccessor, namedSuccessorBody, namedBoth, namedEither, Formula.binders, hkw] at h
  · have hh := addAt_private b 30 31 32 k h; omega
  · have hh := addAt_private b 30 38 45 k h; omega

theorem map_fixedFrame (b w x y z ys zs : Nat) (hb : 45 < b) (hw : 45 < w) :
    mapNames (sigma x y z ys zs) (fixedFrame b w) = assignedFrame b w x y z ys zs := by
  have hd1 := domainAt_shift (sigma x y z ys zs) b b 31 (sigma_block x y z ys zs b hb)
  have hd2 := domainAt_shift (sigma x y z ys zs) b b 32 (sigma_block x y z ys zs b hb)
  have ha1 := addAt_shift (sigma x y z ys zs) b b 30 31 32 (sigma_block x y z ys zs b hb)
  have ha2 := addAt_shift (sigma x y z ys zs) b b 30 38 45 (sigma_block x y z ys zs b hb)
  simp only [sigma, if_pos] at hd1 hd2 ha1 ha2
  simp only [fixedFrame, assignedFrame, mapNames, hd1, hd2, ha1, ha2]
  simp [namedSuccessor, namedSuccessorBody, namedBoth, namedEither, mapNames,
    sigma, show w ≠ 30 by omega, show w ≠ 31 by omega, show w ≠ 32 by omega,
    show w ≠ 38 by omega, show w ≠ 45 by omega]
end PASoundness.PAtoCompactPAAddSuccDynamicSyntax
#print axioms PASoundness.PAtoCompactPAAddSuccDynamicSyntax.map_fixedFrame
