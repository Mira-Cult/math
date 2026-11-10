import PASoundness.PAtoCompactFirstFactorRenameInputs
import PASoundness.PAtoCompactFirstFactorSuccessorTestRebind
import PASoundness.PAtoCompactScopedActiveReplace

/-! Safely normalize the two large source input labels in a supplied
first-factor successor frame. This is a proof-data transformer; it does not
construct its input frame or any arithmetic witness. -/
namespace PASoundness.PAtoCompactFirstFactorNormalizeInputs

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFreeNames
open PASoundness.PAtoCompactTermGraphBinderRange PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactLiteralCutBaseSyntax
open PASoundness.PAtoCompactLiteralCutOutputSyntax PASoundness.PAtoCompactLiteralCutAdditionDefinition
open PASoundness.PAtoCompactFirstFactorOutputAlpha PASoundness.PAtoCompactFirstFactorRenameSyntax
open PASoundness.PAtoCompactFirstFactorSuccessorTestRebind
open PASoundness.PAtoCompactTemplateBlockShift PASoundness.PAtoCompactAlphaMapOne
open PASoundness.PAtoCompactMapNamesCongr
open PASoundness.PAtoCompactScopedActiveReplace

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A low name distinct from both explicit binders is not bound in the
assigned frame, irrespective of aliases among the four free labels. -/
theorem outside_assigned_binders (b r w x y p s k : Nat)
    (hk : k < b+2) (hkr : k ≠ r) (hkw : k ≠ w) :
    k ∉ (assignedFrame b r w x y p s).binders := by
  have hBody : k ∉ (body b p y s r).binders := by
    intro h
    simp only [body, andF_binders, Finset.mem_union] at h
    rcases h with hd | hc | ha | hm
    · have hh := domainAt_private b r k hd; omega
    · have hh := literalCutAt_private b p y r k hc; omega
    · have hh := addAt_private b p y r k ha; omega
    · have hh := mulAt_private b s y r k hm; omega
  intro h
  simp only [assignedFrame, Formula.binders, Finset.mem_union, Finset.mem_insert] at h
  rcases h with hd1 | hd2 | hd3 | hs | hm | hr | hbody
  · have hh := domainAt_private b x k hd1; omega
  · have hh := domainAt_private b y k hd2; omega
  · have hh := domainAt_private b p k hd3; omega
  · simp [namedSuccessor, namedSuccessorBody, namedBoth, namedEither, Formula.binders, hkw] at hs
  · have hh := mulAt_private b x y p k hm; omega
  · exact hkr hr
  · exact hBody hbody

private theorem literal_shift (g : Nat → Nat) (b p y q : Nat)
    (hg : ∀ i < 64, g (b+i) = b+i) :
    mapNames g (literalCutAt b p y q) = literalCutAt b (g p) (g y) (g q) := by
  unfold literalCutAt
  apply threeMap_shift
  · decide
  · exact hg

/-- A map fixing the private block and both local binders acts on precisely
the four frame inputs. -/
theorem map_assigned (g : Nat → Nat) (b r w x y p s : Nat)
    (hg : ∀ i < 64, g (b+i) = b+i) (hr : g r = r) (hw : g w = w) :
    mapNames g (assignedFrame b r w x y p s) =
      assignedFrame b r w (g x) (g y) (g p) (g s) := by
  have hd1 := domainAt_shift g b b x hg
  have hd2 := domainAt_shift g b b y hg
  have hd3 := domainAt_shift g b b p hg
  have hdr := domainAt_shift g b b r hg
  have hm1 := mulAt_shift g b b x y p hg
  have hm2 := mulAt_shift g b b s y r hg
  have ha := addAt_shift g b b p y r hg
  have hc := literal_shift g b p y r hg
  simp only [assignedFrame, mapNames, body, mapNames_andF, hd1, hd2, hd3,
    hdr, hm1, hm2, ha, hc]
  simp [namedSuccessor, namedSuccessorBody, namedBoth, namedEither, Formula.ex,
    Formula.not, mapNames, hr, hw]

/-- A low input replacement is capture-safe provided the replaced name and
the target name are absent from both binder sets; this syntactic equation
records how all four input positions change. -/
theorem replace_assigned (b r w x y p s a z : Nat)
    (ha : a < b) (har : a ≠ r) (haw : a ≠ w) :
    replace a z (assignedFrame b r w x y p s) =
      assignedFrame b r w (rename a z x) (rename a z y)
        (rename a z p) (rename a z s) := by
  have hn := outside_assigned_binders b r w x y p s a (by omega) har haw
  rw [← map_eq_replace a z _ hn]
  apply map_assigned
  · intro i hi
    simp [rename, show b+i ≠ a by omega]
  · simp [rename, Ne.symm har]
  · simp [rename, Ne.symm haw]

/-- For fresh local binders r,w and a high allocator, normalize source
labels 204→31 and 205→38. The other source labels 30,32 and the common
output binder r remain unchanged. -/
def normalize_inputs (b r w : Nat)
    (hb : 205 < b) (hr : 205 < r) (hw : 205 < w)
    (d : KDerivation (assignedFrame b r w 204 30 32 205).encode) :
    KDerivation (fixedFrame b r w).encode := by
  let f := assignedFrame b r w 204 30 32 205
  have hd1 := replace_derivation 204 31 f
    (outside_assigned_binders b r w 204 30 32 205 204 (by omega) (by omega) (by omega))
    (outside_assigned_binders b r w 204 30 32 205 31 (by omega) (by omega) (by omega)) d
  have hshape1 : replace 204 31 f = assignedFrame b r w 31 30 32 205 := by
    dsimp [f]
    rw [replace_assigned b r w 204 30 32 205 204 31 (by omega) (by omega) (by omega)]
    simp [rename]
  rw [hshape1] at hd1
  let g := assignedFrame b r w 31 30 32 205
  have hd2 := replace_derivation 205 38 g
    (outside_assigned_binders b r w 31 30 32 205 205 (by omega) (by omega) (by omega))
    (outside_assigned_binders b r w 31 30 32 205 38 (by omega) (by omega) (by omega)) hd1
  have hshape2 : replace 205 38 g = fixedFrame b r w := by
    dsimp [g]
    rw [replace_assigned b r w 31 30 32 205 205 38 (by omega) (by omega) (by omega)]
    simp [rename, assignedFrame, fixedFrame]
  rwa [hshape2] at hd2

theorem normalize_inputs_certificate (b r w : Nat)
    (hb : 205 < b) (hr : 205 < r) (hw : 205 < w)
    (d : KDerivation (assignedFrame b r w 204 30 32 205).encode) :
    theoremCode (certificate (normalize_inputs b r w hb hr hw d)) =
      (fixedFrame b r w).encode := certificate_correct _

end PASoundness.PAtoCompactFirstFactorNormalizeInputs

#print axioms PASoundness.PAtoCompactFirstFactorNormalizeInputs.outside_assigned_binders
#print axioms PASoundness.PAtoCompactFirstFactorNormalizeInputs.map_assigned
#print axioms PASoundness.PAtoCompactFirstFactorNormalizeInputs.replace_assigned
#print axioms PASoundness.PAtoCompactFirstFactorNormalizeInputs.normalize_inputs
#print axioms PASoundness.PAtoCompactFirstFactorNormalizeInputs.normalize_inputs_certificate
