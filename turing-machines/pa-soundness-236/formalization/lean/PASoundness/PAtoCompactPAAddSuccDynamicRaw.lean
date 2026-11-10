import PASoundness.PAtoCompactPAAddSuccDynamicSyntax
import PASoundness.PAtoCompactPAAddSuccFiveRename
import PASoundness.PAtoCompactPAAddSuccFreshTest

/-! Capture-safe arbitrary-label finite K addition-successor compatibility
for the raw successor relation. This is not yet quotient successor or a PA
axiom translation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPAAddSuccDynamicRaw
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactPAAddSuccDynamicSyntax PASoundness.PAtoCompactPAAddSuccFiveRename
open PASoundness.PAtoCompactPAAddSuccFreshTest PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactZeroSuccessor

/-- The test name w is fresh for all operands. Operand labels may alias, and
all names lie below the private allocator block. -/
noncomputable def dynamic_raw_step (b w x y z ys zs : Nat)
    (hb : 46 ≤ b) (hw : 45 < w)
    (hx : x < b+2) (hy : y < b+2) (hz : z < b+2)
    (hys : ys < b+2) (hzs : zs < b+2)
    (hxw : x ≠ w) (hyw : y ≠ w) (hzw : z ≠ w)
    (hysw : ys ≠ w) (hzsw : zs ≠ w) :
    KDerivation (assignedFrame b w x y z ys zs).encode := by
  let f := fixedFrame b w
  let q := max 45 (max x (max y (max z (max ys (max zs (f.names.sup id)))))) + 1
  have hq : 45 < q := by dsimp [q]; omega
  have hxq : x < q := by dsimp [q]; omega
  have hyq : y < q := by dsimp [q]; omega
  have hzq : z < q := by dsimp [q]; omega
  have hysq : ys < q := by dsimp [q]; omega
  have hzsq : zs < q := by dsimp [q]; omega
  have hqn : ∀ i, i < 5 → q+i ∉ f.names := by
    intro i hi hmem
    have hh : q+i ≤ f.names.sup id := Finset.le_sup (f := id) hmem
    dsimp [q] at hh
    omega
  have h30 : 30 ∉ f.binders := outside_binders b w 30 (by omega) (by omega)
  have h31 : 31 ∉ f.binders := outside_binders b w 31 (by omega) (by omega)
  have h32 : 32 ∉ f.binders := outside_binders b w 32 (by omega) (by omega)
  have h38 : 38 ∉ f.binders := outside_binders b w 38 (by omega) (by omega)
  have h45 : 45 ∉ f.binders := outside_binders b w 45 (by omega) (by omega)
  have hxB : x ∉ f.binders := outside_binders b w x hx hxw
  have hyB : y ∉ f.binders := outside_binders b w y hy hyw
  have hzB : z ∉ f.binders := outside_binders b w z hz hzw
  have hysB : ys ∉ f.binders := outside_binders b w ys hys hysw
  have hzsB : zs ∉ f.binders := outside_binders b w zs hzs hzsw
  have hsource : KDerivation f.encode := by
    have h := fixed_fresh_test_step b w hb (by omega) (by omega) (by omega) (by omega)
    simpa [f, fixedFrame, Formula.encode, namedSuccessor, namedSuccessorBody,
      namedBoth, namedEither, successorCode, CompactProof.both, CompactProof.neg,
      PASoundness.CompactDerivations.either] using h
  have hd := simultaneous_derivation f q x y z ys zs hq hxq hyq hzq hysq hzsq
    h30 h31 h32 h38 h45 hxB hyB hzB hysB hzsB hqn hsource
  change KDerivation (mapNames (sigma x y z ys zs) (fixedFrame b w)).encode at hd
  rw [map_fixedFrame b w x y z ys zs (by omega) hw] at hd
  exact hd

theorem dynamic_raw_step_certificate (b w x y z ys zs : Nat)
    (hb : 46 ≤ b) (hw : 45 < w)
    (hx : x < b+2) (hy : y < b+2) (hz : z < b+2)
    (hys : ys < b+2) (hzs : zs < b+2)
    (hxw : x ≠ w) (hyw : y ≠ w) (hzw : z ≠ w)
    (hysw : ys ≠ w) (hzsw : zs ≠ w) :
    theoremCode (certificate (dynamic_raw_step b w x y z ys zs hb hw hx hy hz hys hzs
      hxw hyw hzw hysw hzsw)) = (assignedFrame b w x y z ys zs).encode := certificate_correct _
/-- A test label outside all five operands; it need not lie in the template
allocation block because its quantifier scope is local to the raw successor. -/
def freshTest (x y z ys zs : Nat) : Nat := max 45 (max x (max y (max z (max ys zs)))) + 1

/-- The same arbitrary-label result with the test name chosen internally.
Operand aliases, including swapped and identical names, are allowed. -/
noncomputable def dynamic_raw_auto (b x y z ys zs : Nat)
    (hb : 46 ≤ b) (hx : x < b+2) (hy : y < b+2) (hz : z < b+2)
    (hys : ys < b+2) (hzs : zs < b+2) :
    KDerivation (assignedFrame b (freshTest x y z ys zs) x y z ys zs).encode := by
  apply dynamic_raw_step b (freshTest x y z ys zs) x y z ys zs hb
    (by unfold freshTest; omega) hx hy hz hys hzs <;> unfold freshTest <;> omega

theorem dynamic_raw_auto_certificate (b x y z ys zs : Nat)
    (hb : 46 ≤ b) (hx : x < b+2) (hy : y < b+2) (hz : z < b+2)
    (hys : ys < b+2) (hzs : zs < b+2) :
    theoremCode (certificate (dynamic_raw_auto b x y z ys zs hb hx hy hz hys hzs)) =
      (assignedFrame b (freshTest x y z ys zs) x y z ys zs).encode := certificate_correct _
end PASoundness.PAtoCompactPAAddSuccDynamicRaw
#print axioms PASoundness.PAtoCompactPAAddSuccDynamicRaw.dynamic_raw_step
#print axioms PASoundness.PAtoCompactPAAddSuccDynamicRaw.dynamic_raw_step_certificate
