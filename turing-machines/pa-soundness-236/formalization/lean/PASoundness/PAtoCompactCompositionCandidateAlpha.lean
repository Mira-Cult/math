import PASoundness.PAtoCompactCandidateFieldTransport

/-! Exact K alpha conversion between the candidate witness-binder names used
by the composition and symmetry constructions. This does not establish graph
collection, quotient laws, or a PA proof interpretation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCompositionCandidateAlpha
open PASoundness.CompactProof PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactCandidateFieldTransport

/-- Replace the least/greatest witness binder 13 by fresh binder 10. -/
def composition_to_symmetry : KDerivation
    (imp (candidateCode 0 37 32 33 34 30 35 13 36)
      (candidateCode 0 37 32 33 34 30 35 10 36)) :=
  witness_field 0 37 32 33 34 30 35 13 36 10 (by decide) (by decide)

/-- The reverse replacement is a separate literal K derivation. -/
def symmetry_to_composition : KDerivation
    (imp (candidateCode 0 37 32 33 34 30 35 10 36)
      (candidateCode 0 37 32 33 34 30 35 13 36)) :=
  witness_field 0 37 32 33 34 30 35 10 36 13 (by decide) (by decide)

theorem composition_to_symmetry_certificate :
    theoremCode (certificate composition_to_symmetry) =
      imp (candidateCode 0 37 32 33 34 30 35 13 36)
        (candidateCode 0 37 32 33 34 30 35 10 36) :=
  certificate_correct composition_to_symmetry

theorem symmetry_to_composition_certificate :
    theoremCode (certificate symmetry_to_composition) =
      imp (candidateCode 0 37 32 33 34 30 35 10 36)
        (candidateCode 0 37 32 33 34 30 35 13 36) :=
  certificate_correct symmetry_to_composition

end PASoundness.PAtoCompactCompositionCandidateAlpha

#print axioms PASoundness.PAtoCompactCompositionCandidateAlpha.composition_to_symmetry
#print axioms PASoundness.PAtoCompactCompositionCandidateAlpha.symmetry_to_composition
#print axioms PASoundness.PAtoCompactCompositionCandidateAlpha.composition_to_symmetry_certificate
#print axioms PASoundness.PAtoCompactCompositionCandidateAlpha.symmetry_to_composition_certificate
