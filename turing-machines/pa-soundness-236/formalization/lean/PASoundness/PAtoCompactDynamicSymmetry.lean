import PASoundness.PAtoCompactDynamicSymmetryRelocate
import PASoundness.PAtoCompactDynamicSymmetryInstantiate
import PASoundness.PAtoCompactDynamicSymmetryRebase

/-! Candidate-relative symmetry of the quotient relation at dynamically
allocated operand names. This constructs finite K proof data from the fixed
symmetry proof by capture-safe relocation, instantiation and rebasing. -/
namespace PASoundness.PAtoCompactDynamicSymmetry

open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactDynamicSymmetryRebase

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Candidate-relative symmetry for arbitrary operand names below the private
block. The names `x` and `y` may coincide. -/
def dynamic_symmetry (b x y : Nat) (hx : x < b+2) (hy : y < b+2) :
    KDerivation (imp (domainAt b x).encode
      (imp (equivAt b x y).encode (equivAt b y x).encode)) := by
  let q := max x y + 20
  let d := max b q + 100
  let e := d + 100
  have hq8 : q ≠ 8 := by dsimp [q]; omega
  have hq1 : q ≠ 1 := by dsimp [q]; omega
  have hqx : q ≠ x := by dsimp [q]; omega
  have hqy : q ≠ y := by dsimp [q]; omega
  have hd : 100 ≤ d := by dsimp [d]; omega
  have he : d + 100 ≤ e := by dsimp [e]; omega
  have hfixed := PAtoCompactDynamicSymmetryRelocate.relocated_symmetry d e hd he
  have hi := PAtoCompactDynamicSymmetryInstantiate.instantiate_frame d e x y q
    (by dsimp [d, q]; omega) (by dsimp [e, d, q]; omega) hq8 hq1 hqx hqy
    (by simpa [PAtoCompactDynamicSymmetryInstantiate.frame,
      PAtoCompactDynamicSymmetryRelocate.frame] using hfixed)
  apply rebase_symmetry b d e x y hx hy (by dsimp [d, q]; omega)
    (by dsimp [e, d, q]; omega) (by dsimp [e, d, q]; omega)
  simpa [PAtoCompactDynamicSymmetryInstantiate.frame, Formula.encode] using hi

theorem dynamic_symmetry_certificate (b x y : Nat) (hx : x < b+2) (hy : y < b+2) :
    theoremCode (certificate (dynamic_symmetry b x y hx hy)) =
      imp (domainAt b x).encode (imp (equivAt b x y).encode (equivAt b y x).encode) :=
  certificate_correct _

#print axioms dynamic_symmetry
#print axioms dynamic_symmetry_certificate
end PASoundness.PAtoCompactDynamicSymmetry
