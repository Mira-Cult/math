import PASoundness.PAtoCompactMultiplicationAnchoredLocal
import PASoundness.PAtoCompactMultiplicationCandidateTotalityFromLocal

/-! A conditional finite K reduction of candidate multiplication-output
existence to the explicit anchored graph-extension obligation. The anchored
addition witness, first-factor induction, and zero base are supplied by the
imported constructors. The graph-extension derivation remains a proof input;
this module does not establish multiplication totality or the PA bridge. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationCandidateTotalityFromAnchored
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactMultiplicationAnchoredLocal
open PASoundness.PAtoCompactMultiplicationCandidateTotalityFromLocal
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- A finite K proof of the explicit anchored graph extension yields a finite
K proof of candidate-guarded product-output existence at the displayed names.
The graph-extension proof remains an input. -/
def candidate_totality_from_anchored (extension : KDerivation graphExtensionCode) :
    KDerivation (imp (domainAt 300 200).encode (imp (domainAt 300 30).encode
      (existsCode 32 (andF (domainAt 300 32) (mulAt 300 200 30 32)).encode))) :=
  candidate_totality_from_local (local_successor_of_extension extension)

theorem candidate_totality_from_anchored_certificate (extension : KDerivation graphExtensionCode) :
    theoremCode (certificate (candidate_totality_from_anchored extension)) =
      imp (domainAt 300 200).encode (imp (domainAt 300 30).encode
        (existsCode 32 (andF (domainAt 300 32) (mulAt 300 200 30 32)).encode)) :=
  certificate_correct (candidate_totality_from_anchored extension)
end PASoundness.PAtoCompactMultiplicationCandidateTotalityFromAnchored
#print axioms PASoundness.PAtoCompactMultiplicationCandidateTotalityFromAnchored.candidate_totality_from_anchored
#print axioms PASoundness.PAtoCompactMultiplicationCandidateTotalityFromAnchored.candidate_totality_from_anchored_certificate
