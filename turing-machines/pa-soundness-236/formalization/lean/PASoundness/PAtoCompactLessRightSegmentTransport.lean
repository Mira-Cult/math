import PASoundness.PAtoCompactEquivalentEndpointAlias
import PASoundness.PAtoCompactLessRightSegmentOutputVacuity
import PASoundness.PAtoCompactBijectionForwardImage
import PASoundness.PAtoCompactBijectionVacuity
import PASoundness.PAtoCompactOrderIsoVacuity
import PASoundness.PAtoCompactTransitiveWitness

/-! Build the canonical member-transport witness from a supplied actual K
segment restriction proof, retaining all its object-level hypotheses. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLessRightSegmentTransport
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactTransitiveWitness PASoundness.PAtoCompactBijectionForwardImage
open PASoundness.PAtoCompactBijectionVacuity PASoundness.PAtoCompactOrderIsoVacuity
open PASoundness.PAtoCompactEquivalentAliasInstantiation PASoundness.PAtoCompactEquivalentAliasGuardLift
open PASoundness.PAtoCompactRestrictedEquivalentTarget
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def image5 : Formula := namedBoth (.member 1 5) (graphFormula 6 2 5)
def result5 : Formula := namedBoth (.member 1 5) (guarded originalAliases)
def result : Formula := .ex 5 result5
def sourceTrans : Nat := transitiveCode 0 11 12
def targetTrans : Nat := transitiveCode 1 16 18
def sourceMember : Nat := member 0 2
def targetMember : Nat := member 1 5
def topEdge : Nat := (graphFormula 6 2 5).encode

theorem image_replace : replace 3 5 image3 = image5 := by decide

/-- The forward image at the segment's required name 5. -/
def forward_image5 : KDerivation
    (imp bijectionFormula.encode (imp (member 0 2) (existsCode 5 image5.encode))) := by
  have ha := (existentialAlpha 3 5 image3 (by decide) (by decide) (by decide)).1
  rw [image_replace] at ha
  exact compose forward_image (implicationCongr (CompactHilbertBasis.identity _) ha)

/-- Under an explicitly supplied finite K segment-to-endpoint derivation,
construct the canonical member-transport proof. Both transitivity and member
guards remain object-level assumptions. -/
def canonical_transport
    (segment : KDerivation (imp sourceTrans (imp targetTrans (imp sourceMember
      (imp targetMember (imp orderFormula.encode (imp topEdge
        (imp bijectionFormula.encode endpointTarget.encode)))))))) :
    KDerivation (imp sourceTrans (imp targetTrans (imp sourceMember
      (imp equivalentFormula.encode result.encode)))) := by
  let A := sourceTrans
  let B := targetTrans
  let C := sourceMember
  let O := orderFormula.encode
  let I := bijectionFormula.encode
  let W := image5.encode
  let R := result.encode
  let Γ := [I,O,C,B,A]
  have hv : ∀ z, z ∈ Γ → KDerivation (imp z (allCode 5 z)) := by
    intro z hz
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hz
    by_cases hi : z = I
    · subst z
      exact vacuity_of_equiv bijectionFormula freshBijection.formula freshBijection.equivalent 5 (by decide)
    by_cases ho : z = O
    · subst z; exact order_vacuity 5 order_fresh_5
    by_cases hc : z = C
    · subst z; exact membershipVacuity 0 2 5 (by decide) (by decide)
    by_cases hb : z = B
    · subst z; exact transitive_vacuity 1 16 18 5 (by decide) (by decide) (by decide)
    have ha : z = A := by simp_all
    subst z
    exact transitive_vacuity 0 11 12 5 (by decide) (by decide) (by decide)
  have hpoint : Context Γ (imp W result5.encode) := by
    apply Context.deduction
    let Δ := W :: Γ
    have hw : Context Δ W := .head _ _
    have hm : Context Δ (member 1 5) := Context.conjunctionLeft hw
    have he : Context Δ topEdge := Context.conjunctionRight hw
    have hi : Context Δ I := .hypothesis (by simp [Δ,Γ])
    have ho : Context Δ O := .hypothesis (by simp [Δ,Γ])
    have hc : Context Δ C := .hypothesis (by simp [Δ,Γ])
    have hb : Context Δ B := .hypothesis (by simp [Δ,Γ])
    have ha : Context Δ A := .hypothesis (by simp [Δ,Γ])
    have ht : Context Δ endpointTarget.encode :=
      .mp hi (.mp he (.mp ho (.mp hm (.mp hc (.mp hb (.mp ha (.closed segment)))))))
    have heq : Context Δ (guarded originalAliases).encode :=
      .mp ht (.closed PASoundness.PAtoCompactEquivalentEndpointAlias.backward)
    exact Context.conjunctionIntro hm heq
  have hall : Context Γ (allCode 5 (imp W result5.encode)) := Context.generalize 5 hv hpoint
  have hex : Context Γ (existsCode 5 W) := by
    have hi : Context Γ I := .hypothesis (by simp [Γ])
    have hc : Context Γ C := .hypothesis (by simp [Γ])
    exact .mp hc (.mp hi (.closed forward_image5))
  have hres : Context Γ R := exists_map_context hall hex
  have himp : Context [C,B,A] (imp O (imp I R)) :=
    Context.deduction (Context.deduction hres)
  have hmatrix : Context [both I O,C,B,A] R := by
    have hboth : Context [both I O,C,B,A] (both I O) := .head _ _
    have hi : Context [both I O,C,B,A] I := Context.conjunctionLeft hboth
    have ho : Context [both I O,C,B,A] O := Context.conjunctionRight hboth
    exact .mp hi (.mp ho (Context.under himp (both I O)))
  have hmatrixImp : Context [C,B,A] (imp (both I O) R) := Context.deduction hmatrix
  have hall6 : Context [C,B,A] (allCode 6 (imp (both I O) R)) := Context.generalize 6 (by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    by_cases hc : z = C
    · subst z; exact membershipVacuity 0 2 6 (by decide) (by decide)
    by_cases hb : z = B
    · subst z; exact transitive_vacuity 1 16 18 6 (by decide) (by decide) (by decide)
    have ha : z = A := by simp_all
    subst z
    exact transitive_vacuity 0 11 12 6 (by decide) (by decide) (by decide)) hmatrixImp
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Δ := [equivalentFormula.encode,C,B,A]
  have hall' : Context Δ (allCode 6 (imp (both I O) R)) := Context.under hall6 _
  have he : Context Δ (existsCode 6 (both I O)) := by
    have h := Context.head [C,B,A] equivalentFormula.encode
    exact h
  have hvR : KDerivation (imp result.encode (allCode 6 result.encode)) :=
    PASoundness.PAtoCompactLessRightSegmentOutputVacuity.output_vacuity6
  exact Context.existsElim hvR hall' he

theorem canonical_transport_certificate
    (segment : KDerivation (imp sourceTrans (imp targetTrans (imp sourceMember
      (imp targetMember (imp orderFormula.encode (imp topEdge
        (imp bijectionFormula.encode endpointTarget.encode)))))))) :
    theoremCode (certificate (canonical_transport segment)) =
      imp sourceTrans (imp targetTrans (imp sourceMember
        (imp equivalentFormula.encode result.encode))) :=
  certificate_correct (canonical_transport segment)

end PASoundness.PAtoCompactLessRightSegmentTransport

#print axioms PASoundness.PAtoCompactLessRightSegmentTransport.forward_image5
#print axioms PASoundness.PAtoCompactLessRightSegmentTransport.canonical_transport
#print axioms PASoundness.PAtoCompactLessRightSegmentTransport.canonical_transport_certificate
