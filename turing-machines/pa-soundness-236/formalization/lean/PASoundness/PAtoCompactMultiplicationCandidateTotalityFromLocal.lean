import PASoundness.PAtoCompactMultiplicationLocalPoint
import PASoundness.PAtoCompactMultiplicationCandidateTotalityFromPoint

/-! Candidate multiplication-output existence from a supplied local successor
witness constructor. The constructor is an explicit finite K proof input;
this module does not prove the multiplication graph extension or totality. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationCandidateTotalityFromLocal
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactMultiplicationLocalPoint
open PASoundness.PAtoCompactMultiplicationCandidateTotalityFromPoint
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- A local multiplication-successor output proof yields a candidate product
for the displayed allocated candidate inputs. The local proof remains an
explicit assumption and must be constructed separately in K. -/
def candidate_totality_from_local
    (hstep : KDerivation (imp (domainAt 300 204).encode
      (imp (domainAt 300 30).encode (imp (domainAt 300 32).encode
        (imp (successorCode 204 205 208) (imp (mulAt 300 204 30 32).encode
          (existsCode 45 newOutput45.encode))))))) :
    KDerivation (imp (domainAt 300 200).encode (imp (domainAt 300 30).encode
      (existsCode 32 (andF (domainAt 300 32) (mulAt 300 200 30 32)).encode))) :=
  candidate_totality_from_point (guarded_point hstep)

theorem candidate_totality_from_local_certificate
    (hstep : KDerivation (imp (domainAt 300 204).encode
      (imp (domainAt 300 30).encode (imp (domainAt 300 32).encode
        (imp (successorCode 204 205 208) (imp (mulAt 300 204 30 32).encode
          (existsCode 45 newOutput45.encode))))))) :
    theoremCode (certificate (candidate_totality_from_local hstep)) =
      imp (domainAt 300 200).encode (imp (domainAt 300 30).encode
        (existsCode 32 (andF (domainAt 300 32) (mulAt 300 200 30 32)).encode)) :=
  certificate_correct (candidate_totality_from_local hstep)
end PASoundness.PAtoCompactMultiplicationCandidateTotalityFromLocal
#print axioms PASoundness.PAtoCompactMultiplicationCandidateTotalityFromLocal.candidate_totality_from_local
#print axioms PASoundness.PAtoCompactMultiplicationCandidateTotalityFromLocal.candidate_totality_from_local_certificate
