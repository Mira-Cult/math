import PASoundness.PAtoCompactDynamicTransRebase
import PASoundness.PAtoCompactDynamicTransInstantiate

/-! Finite K proof of candidate-relative quotient transitivity at arbitrary
operand names below the private allocation block. Operand names may alias. -/
namespace PASoundness.PAtoCompactDynamicTransitivityFinal

open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactDynamicTransRebase

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Candidate-relative transitivity of the quotient isomorphism relation.
All three operand labels may be identical. -/
def dynamic_transitivity (b x y z : Nat)
    (hx : x < b + 2) (hy : y < b + 2) (hz : z < b + 2) :
    KDerivation (imp (domainAt b x).encode
      (imp (equivAt b x y).encode
        (imp (equivAt b y z).encode (equivAt b x z).encode))) := by
  let q := max (max (max 8 x) y) z + 1
  let d := max b q + 100
  let e := d + 100
  have hf := PAtoCompactDynamicTransRelocation.relocated_transitivity d e
    (by dsimp [d, q]; omega) (by dsimp [e]; omega)
  have hi := PAtoCompactDynamicTransInstantiate.instantiate_frame d e x y z q
    (by dsimp [q]; omega) (by dsimp [d, q]; omega) (by dsimp [e, d, q]; omega)
    (by simpa only [PAtoCompactDynamicTransInstantiate.frame,
      PAtoCompactDynamicTransRelocation.transFrame] using hf)
  have hr := trans_rebase b d e x y z hx hy hz
    (by dsimp [d, q]; omega) (by dsimp [e, d, q]; omega)
    (by dsimp [e, d, q]; omega) (by dsimp [e, d, q]; omega)
    (by simpa only [PAtoCompactDynamicTransInstantiate.frame,
      PAtoCompactDynamicTransRelocation.transFrame] using hi)
  simpa only [PAtoCompactDynamicTransRelocation.transFrame, Formula.encode] using hr

theorem dynamic_transitivity_certificate (b x y z : Nat)
    (hx : x < b + 2) (hy : y < b + 2) (hz : z < b + 2) :
    theoremCode (certificate (dynamic_transitivity b x y z hx hy hz)) =
      imp (domainAt b x).encode (imp (equivAt b x y).encode
        (imp (equivAt b y z).encode (equivAt b x z).encode)) := certificate_correct _

end PASoundness.PAtoCompactDynamicTransitivityFinal

#print axioms PASoundness.PAtoCompactDynamicTransitivityFinal.dynamic_transitivity
#print axioms PASoundness.PAtoCompactDynamicTransitivityFinal.dynamic_transitivity_certificate
