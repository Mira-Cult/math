import PASoundness.PAtoCompactRestrictedEquivalentTarget
import PASoundness.PAtoCompactRestrictionWitnessEight
import PASoundness.PAtoCompactTransitiveWitness

/-! Elimination of the supplied endpoint filter from an arbitrary-initial-
segment matrix proof. The matrix derivation remains an explicit proof-data
premise; this module alone does not prove initial-segment restriction. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSegmentMatrixExists
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactTransitiveWitness PASoundness.PAtoCompactRestrictedMatrix
open PASoundness.PAtoCompactRestrictedOrderPoint PASoundness.PAtoCompactRestrictionWitnessEight
open PASoundness.PAtoCompactRestrictedEquivalentTarget
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def sourceTrans : Nat := transitiveCode 0 11 12
def targetTrans : Nat := transitiveCode 1 16 18
def sourceMember : Nat := member 0 2
def targetMember : Nat := member 1 5
def topEdge : Nat := (graphFormula 6 2 5).encode

/-- An explicit K proof of the arbitrary-segment matrix entails an
isomorphism between the prepared endpoint formulas, after constructing and
eliminating the endpoint filter. All object-level hypotheses are retained. -/
def segment_target_of_matrix
    (step : KDerivation (imp sourceTrans (imp targetTrans (imp sourceMember
      (imp targetMember (imp orderFormula.encode (imp filter (imp topEdge
        (imp bijectionFormula.encode restrictedMatrix))))))))) :
    KDerivation (imp sourceTrans (imp targetTrans (imp sourceMember
      (imp targetMember (imp orderFormula.encode (imp topEdge
        (imp bijectionFormula.encode endpointTarget.encode))))))) := by
  let A := sourceTrans
  let B := targetTrans
  let C := sourceMember
  let D := targetMember
  let O := orderFormula.encode
  let E := topEdge
  let I := bijectionFormula.encode
  let Γ := [I,E,O,D,C,B,A]
  have hv : ∀ z, z ∈ Γ → KDerivation (imp z (allCode 8 z)) := by
    intro z hz
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hz
    by_cases he : z = I
    · subst z; exact bijectionFormula.vacuity 8 (by decide)
    by_cases he : z = E
    · subst z; exact (graphFormula 6 2 5).vacuity 8 (by decide)
    by_cases he : z = O
    · subst z; exact orderFormula.vacuity 8 (by decide)
    by_cases he : z = D
    · subst z; exact membershipVacuity 1 5 8 (by decide) (by decide)
    by_cases he : z = C
    · subst z; exact membershipVacuity 0 2 8 (by decide) (by decide)
    by_cases he : z = B
    · subst z; exact transitive_vacuity 1 16 18 8 (by decide) (by decide) (by decide)
    have he : z = A := by simp_all
    subst z
    exact transitive_vacuity 0 11 12 8 (by decide) (by decide) (by decide)
  have hs : Context Γ (imp filter restrictedMatrix) := by
    apply Context.deduction
    let Δ := filter :: Γ
    have hf : Context Δ filter := .head _ _
    have hi : Context Δ I := .hypothesis (by simp [Δ,Γ])
    have he : Context Δ E := .hypothesis (by simp [Δ,Γ])
    have ho : Context Δ O := .hypothesis (by simp [Δ,Γ])
    have hd : Context Δ D := .hypothesis (by simp [Δ,Γ])
    have hc : Context Δ C := .hypothesis (by simp [Δ,Γ])
    have hb : Context Δ B := .hypothesis (by simp [Δ,Γ])
    have ha : Context Δ A := .hypothesis (by simp [Δ,Γ])
    exact .mp hi (.mp he (.mp hf (.mp ho (.mp hd (.mp hc (.mp hb (.mp ha (.closed step))))))))
  have hall : Context Γ (allCode 8 (imp filter restrictedMatrix)) := Context.generalize 8 hv hs
  have hex : Context Γ (existsCode 8 restrictedMatrix) :=
    exists_map_context hall (.closed restriction_exists_eight)
  have ht : Context Γ endpointTarget.encode := .mp hex (.closed restricted_to_target)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact ht

theorem segment_target_of_matrix_certificate
    (step : KDerivation (imp sourceTrans (imp targetTrans (imp sourceMember
      (imp targetMember (imp orderFormula.encode (imp filter (imp topEdge
        (imp bijectionFormula.encode restrictedMatrix))))))))) :
    theoremCode (certificate (segment_target_of_matrix step)) =
      imp sourceTrans (imp targetTrans (imp sourceMember
        (imp targetMember (imp orderFormula.encode (imp topEdge
          (imp bijectionFormula.encode endpointTarget.encode)))))) :=
  certificate_correct (segment_target_of_matrix step)

end PASoundness.PAtoCompactSegmentMatrixExists

#print axioms PASoundness.PAtoCompactSegmentMatrixExists.segment_target_of_matrix
