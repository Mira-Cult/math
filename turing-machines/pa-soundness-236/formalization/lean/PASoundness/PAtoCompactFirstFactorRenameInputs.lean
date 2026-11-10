import PASoundness.PAtoCompactFirstFactorRenameSyntax
import PASoundness.PAtoCompactPAAddSuccFiveRename

/-! Conditional, simultaneous renaming of the four free input labels in a
first-factor multiplication-successor frame. The caller supplies a proof of
the fixed frame; this module does not construct that proof. -/
namespace PASoundness.PAtoCompactFirstFactorRenameInputs

open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactFirstFactorRenameSyntax
open PASoundness.PAtoCompactPAAddSuccDynamicSyntax (sigma)
open PASoundness.PAtoCompactPAAddSuccFiveRename

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Capture-safe simultaneous renaming from a supplied fixed-frame K proof.
The target free input labels may coincide. The locally bound output r and raw
successor test w must be fresh for those labels, but may coincide with each
other since their scopes are separate. -/
def rename_inputs (b r w x y p s : Nat)
    (hb : 45 < b) (hr : 45 < r) (hw : 45 < w)
    (hx : x < b+2) (hy : y < b+2) (hp : p < b+2) (hs : s < b+2)
    (hxr : x ≠ r) (hyr : y ≠ r) (hpr : p ≠ r) (hsr : s ≠ r)
    (hxw : x ≠ w) (hyw : y ≠ w) (hpw : p ≠ w) (hsw : s ≠ w)
    (d : KDerivation (fixedFrame b r w).encode) :
    KDerivation (assignedFrame b r w x y p s).encode := by
  let f := fixedFrame b r w
  let q := max 45 (max x (max y (max p (max s (f.names.sup id))))) + 1
  have hq : 45 < q := by dsimp [q]; omega
  have hxq : x < q := by dsimp [q]; omega
  have hyq : y < q := by dsimp [q]; omega
  have hpq : p < q := by dsimp [q]; omega
  have hsq : s < q := by dsimp [q]; omega
  have hqn : ∀ i, i < 5 → q+i ∉ f.names := by
    intro i hi hmem
    have hh : q+i ≤ f.names.sup id := Finset.le_sup (f := id) hmem
    dsimp [q] at hh
    omega
  have h30 : 30 ∉ f.binders := outside_binders b r w 30 (by omega) (by omega) (by omega)
  have h31 : 31 ∉ f.binders := outside_binders b r w 31 (by omega) (by omega) (by omega)
  have h32 : 32 ∉ f.binders := outside_binders b r w 32 (by omega) (by omega) (by omega)
  have h38 : 38 ∉ f.binders := outside_binders b r w 38 (by omega) (by omega) (by omega)
  have h45 : 45 ∉ f.binders := outside_binders b r w 45 (by omega) (by omega) (by omega)
  have hxB : x ∉ f.binders := outside_binders b r w x hx hxr hxw
  have hyB : y ∉ f.binders := outside_binders b r w y hy hyr hyw
  have hpB : p ∉ f.binders := outside_binders b r w p hp hpr hpw
  have hsB : s ∉ f.binders := outside_binders b r w s hs hsr hsw
  have hd := simultaneous_derivation f q y x p s 45 hq hyq hxq hpq hsq (by omega)
    h30 h31 h32 h38 h45 hyB hxB hpB hsB h45 hqn d
  change KDerivation (PASoundness.PAtoCompactTermTranslation.mapNames
    (sigma y x p s 45) (fixedFrame b r w)).encode at hd
  rw [map_fixedFrame b r w x y p s hb hr hw] at hd
  exact hd

theorem rename_inputs_certificate (b r w x y p s : Nat)
    (hb : 45 < b) (hr : 45 < r) (hw : 45 < w)
    (hx : x < b+2) (hy : y < b+2) (hp : p < b+2) (hs : s < b+2)
    (hxr : x ≠ r) (hyr : y ≠ r) (hpr : p ≠ r) (hsr : s ≠ r)
    (hxw : x ≠ w) (hyw : y ≠ w) (hpw : p ≠ w) (hsw : s ≠ w)
    (d : KDerivation (fixedFrame b r w).encode) :
    theoremCode (certificate (rename_inputs b r w x y p s hb hr hw hx hy hp hs
      hxr hyr hpr hsr hxw hyw hpw hsw d)) =
      (assignedFrame b r w x y p s).encode := certificate_correct _

end PASoundness.PAtoCompactFirstFactorRenameInputs

#print axioms PASoundness.PAtoCompactFirstFactorRenameInputs.rename_inputs
#print axioms PASoundness.PAtoCompactFirstFactorRenameInputs.rename_inputs_certificate
