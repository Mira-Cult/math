import PASoundness.PAtoCompactFirstFactorOutputAlpha
import PASoundness.PAtoCompactPAAddSuccDynamicSyntax
import PASoundness.PAtoCompactPAAddSuccFiveRename
import PASoundness.PAtoCompactLiteralCutBaseSyntax
import PASoundness.PAtoCompactTemplateBlockShift

/-! Syntax and binder bounds for simultaneously renaming the four free
inputs of a retained first-factor successor witness. No K proof is asserted. -/
namespace PASoundness.PAtoCompactFirstFactorRenameSyntax

open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactFirstFactorOutputAlpha PASoundness.PAtoCompactLiteralCutBaseSyntax
open PASoundness.PAtoCompactLiteralCutOutputSyntax PASoundness.PAtoCompactLiteralCutAdditionDefinition
open PASoundness.PAtoCompactTemplateBlockShift PASoundness.PAtoCompactMapNamesCongr
open PASoundness.PAtoCompactPAAddSuccDynamicSyntax

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Source free labels are 31,30,32,38; output r and successor-test w are
bound. The two binders need not be distinct because their scopes are separate. -/
def fixedFrame (b r w : Nat) : Formula :=
  .imp (domainAt b 31) (.imp (domainAt b 30) (.imp (domainAt b 32)
    (.imp (namedSuccessor 31 38 w) (.imp (mulAt b 31 30 32)
      (.ex r (body b 32 30 38 r))))))

/-- Desired free inputs may coincide; r remains the one bound output. -/
def assignedFrame (b r w x y p s : Nat) : Formula :=
  .imp (domainAt b x) (.imp (domainAt b y) (.imp (domainAt b p)
    (.imp (namedSuccessor x s w) (.imp (mulAt b x y p)
      (.ex r (body b p y s r))))))

/-- Names below the private block cannot be bound except at the two explicit
local binders r and w. -/
theorem outside_binders (b r w k : Nat) (hk : k < b+2) (hkr : k ≠ r) (hkw : k ≠ w) :
    k ∉ (fixedFrame b r w).binders := by
  have hBody : k ∉ (body b 32 30 38 r).binders := by
    intro h
    simp only [body, andF_binders, Finset.mem_union] at h
    rcases h with hd | hc | ha | hm
    · have hh := domainAt_private b r k hd; omega
    · have hh := literalCutAt_private b 32 30 r k hc; omega
    · have hh := addAt_private b 32 30 r k ha; omega
    · have hh := mulAt_private b 38 30 r k hm; omega
  intro h
  simp only [fixedFrame, Formula.binders, Finset.mem_union, Finset.mem_insert] at h
  rcases h with hd1 | hd2 | hd3 | hs | hm | hr | hbody
  · have hh := domainAt_private b 31 k hd1; omega
  · have hh := domainAt_private b 30 k hd2; omega
  · have hh := domainAt_private b 32 k hd3; omega
  · simp [namedSuccessor, namedSuccessorBody, namedBoth, namedEither, Formula.binders, hkw] at hs
  · have hh := mulAt_private b 31 30 32 k hm; omega
  · exact hkr hr
  · exact hBody hbody

private theorem literal_shift (g : Nat → Nat) (b p y q : Nat)
    (hg : ∀ i < 64, g (b+i) = b+i) :
    mapNames g (literalCutAt b p y q) = literalCutAt b (g p) (g y) (g q) := by
  unfold literalCutAt
  apply threeMap_shift
  · decide
  · exact hg

/-- The staged five-name map acts on the intended four free labels while
leaving the local binders and the private template block fixed. -/
theorem map_fixedFrame (b r w x y p s : Nat) (hb : 45 < b)
    (hr : 45 < r) (hw : 45 < w) :
    mapNames (sigma y x p s 45) (fixedFrame b r w) = assignedFrame b r w x y p s := by
  let g := sigma y x p s 45
  have hblock : ∀ i < 64, g (b+i) = b+i := sigma_block y x p s 45 b hb
  have hd1 := domainAt_shift g b b 31 hblock
  have hd2 := domainAt_shift g b b 30 hblock
  have hd3 := domainAt_shift g b b 32 hblock
  have hdr := domainAt_shift g b b r hblock
  have hm1 := mulAt_shift g b b 31 30 32 hblock
  have hm2 := mulAt_shift g b b 38 30 r hblock
  have ha := addAt_shift g b b 32 30 r hblock
  have hc := literal_shift g b 32 30 r hblock
  have gr : g r = r := by
    simp [g, sigma, show r ≠ 30 by omega, show r ≠ 31 by omega,
      show r ≠ 32 by omega, show r ≠ 38 by omega, show r ≠ 45 by omega]
  simp only [g, sigma, if_pos] at hd1 hd2 hd3 hdr hm1 hm2 ha hc
  simp only [fixedFrame, assignedFrame, mapNames, body, mapNames_andF, hd1, hd2, hd3,
    hdr, hm1, hm2, ha, hc]
  simp [namedSuccessor, namedSuccessorBody, namedBoth, namedEither,
    Formula.not, mapNames, sigma, gr, g, show r ≠ 30 by omega, show r ≠ 31 by omega,
    show r ≠ 32 by omega, show r ≠ 38 by omega, show r ≠ 45 by omega,
    show w ≠ 30 by omega, show w ≠ 31 by omega, show w ≠ 32 by omega,
    show w ≠ 38 by omega, show w ≠ 45 by omega]

end PASoundness.PAtoCompactFirstFactorRenameSyntax

#print axioms PASoundness.PAtoCompactFirstFactorRenameSyntax.fixedFrame
#print axioms PASoundness.PAtoCompactFirstFactorRenameSyntax.assignedFrame
#print axioms PASoundness.PAtoCompactFirstFactorRenameSyntax.outside_binders
#print axioms PASoundness.PAtoCompactFirstFactorRenameSyntax.map_fixedFrame
