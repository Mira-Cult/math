import PASoundness.PAtoCompactFirstFactorSuccessorSharedRebase
import PASoundness.PAtoCompactFirstFactorSuccessorOutputRebind
import PASoundness.PAtoCompactFirstFactorFrameEncoding
import PASoundness.PAtoCompactFirstFactorNormalizeInputs
import PASoundness.PAtoCompactFirstFactorRenameInputs

/-! Move the fixed first-factor successor shared-output proof to arbitrary
possibly aliased input names at a sufficiently high allocator, while keeping
one fresh common-output binder and a fresh raw successor test binder. This is
not yet the guarded PA axiom or the right-factor multiplication law. -/
namespace PASoundness.PAtoCompactFirstFactorHighInputFrame

open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactFirstFactorOutputAlpha PASoundness.PAtoCompactFirstFactorRenameSyntax
open PASoundness.PAtoCompactFirstFactorSuccessorSharedRebase
open PASoundness.PAtoCompactFirstFactorSuccessorTestRebind
open PASoundness.PAtoCompactFirstFactorSuccessorOutputRebind
open PASoundness.PAtoCompactFirstFactorFrameEncoding PASoundness.PAtoCompactFirstFactorNormalizeInputs
open PASoundness.PAtoCompactFirstFactorRenameInputs

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Derive the shared-output frame at arbitrary input labels below a high
allocator. The input labels may coincide. The output and successor test labels
are separately bound, and may coincide with each other; each must differ from
the four input labels. The supplied bounds are naming conditions, not
inequalities of represented values. -/
noncomputable def high_frame (b r w x y p s : Nat)
    (hb : 205 < b) (hr : 208 < r) (hrb : r < b) (hw : 205 < w)
    (hx : x < b+2) (hy : y < b+2) (hp : p < b+2) (hs : s < b+2)
    (hxr : x ≠ r) (hyr : y ≠ r) (hpr : p ≠ r) (hsr : s ≠ r)
    (hxw : x ≠ w) (hyw : y ≠ w) (hpw : p ≠ w) (hsw : s ≠ w) :
    KDerivation (assignedFrame b r w x y p s).encode := by
  have d0 : KDerivation (guardedFrame b 204 30 32 205 45 208) := by
    simpa only [guardedFrame, body, resultBody] using
      PAtoCompactFirstFactorSuccessorSharedRebase.rebase b hb
  have d1 := rebind_output b 204 30 32 205 45 r 208
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) d0
  have d2 := PAtoCompactFirstFactorSuccessorTestRebind.rebind b 204 30 32 205 r 208 w
    (by omega) (by omega) (by omega) (by omega) d1
  have d3 := to_named b r w 204 30 32 205 d2
  have d4 := normalize_inputs b r w hb (by omega) hw d3
  exact rename_inputs b r w x y p s (by omega) (by omega) (by omega)
    hx hy hp hs hxr hyr hpr hsr hxw hyw hpw hsw d4

theorem high_frame_certificate (b r w x y p s : Nat)
    (hb : 205 < b) (hr : 208 < r) (hrb : r < b) (hw : 205 < w)
    (hx : x < b+2) (hy : y < b+2) (hp : p < b+2) (hs : s < b+2)
    (hxr : x ≠ r) (hyr : y ≠ r) (hpr : p ≠ r) (hsr : s ≠ r)
    (hxw : x ≠ w) (hyw : y ≠ w) (hpw : p ≠ w) (hsw : s ≠ w) :
    theoremCode (certificate (high_frame b r w x y p s hb hr hrb hw hx hy hp hs
      hxr hyr hpr hsr hxw hyw hpw hsw)) = (assignedFrame b r w x y p s).encode :=
  certificate_correct _

end PASoundness.PAtoCompactFirstFactorHighInputFrame

#print axioms PASoundness.PAtoCompactFirstFactorHighInputFrame.high_frame
#print axioms PASoundness.PAtoCompactFirstFactorHighInputFrame.high_frame_certificate
