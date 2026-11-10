import PASoundness.PAtoCompactLessRightSegmentTransport
import PASoundness.PAtoCompactSegmentMatrixClosed

/-! A selected proper-cut image and its prepared initial-segment isomorphism,
retaining the edge in the *original* graph. No suffix, whole-cut case, or
addition output-transport theorem is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSelectedCutGraphTransport
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactTransitiveWitness PASoundness.PAtoCompactBijectionVacuity
open PASoundness.PAtoCompactOrderIsoVacuity PASoundness.PAtoCompactRestrictedEquivalentTarget
open PASoundness.PAtoCompactLessRightSegmentTransport
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The selected target cut is a member of the target outer set, is related
by the original graph to the supplied source cut, and has the prepared
isomorphism from that source cut. All three refer to the same name 5. -/
def selectedCutBody : Formula := namedBoth image5 endpointTarget

def selectedCut : Formula := .ex 5 selectedCutBody

/-- Under both outer transitivity guards, source-cut membership, and the
order/bijection matrices for one supplied graph, K constructs a target cut
with the original graph edge and prepared initial-segment isomorphism.
The graph is not existentially eliminated and object values may coincide. -/
def selected_cut_graph_transport : KDerivation
    (imp sourceTrans (imp targetTrans (imp sourceMember
      (imp orderFormula.encode (imp bijectionFormula.encode selectedCut.encode))))) := by
  let A := sourceTrans
  let B := targetTrans
  let C := sourceMember
  let O := orderFormula.encode
  let I := bijectionFormula.encode
  let W := image5.encode
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
  have hpoint : Context Γ (imp W selectedCutBody.encode) := by
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
      .mp hi (.mp he (.mp ho (.mp hm (.mp hc (.mp hb (.mp ha
        (.closed PASoundness.PAtoCompactSegmentMatrixClosed.segment_target)))))))
    simpa only [selectedCutBody, namedBoth, Formula.not, Formula.encode,
      CompactProof.both, CompactProof.neg] using Context.conjunctionIntro hw ht
  have hall : Context Γ (allCode 5 (imp W selectedCutBody.encode)) :=
    Context.generalize 5 hv hpoint
  have hex : Context Γ (existsCode 5 W) := by
    have hi : Context Γ I := .hypothesis (by simp [Γ])
    have hc : Context Γ C := .hypothesis (by simp [Γ])
    exact .mp hc (.mp hi (.closed forward_image5))
  have hres : Context Γ selectedCut.encode := by
    change Context Γ (existsCode 5 selectedCutBody.encode)
    exact exists_map_context hall hex
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact hres

theorem selected_cut_graph_transport_certificate :
    theoremCode (certificate selected_cut_graph_transport) =
      imp sourceTrans (imp targetTrans (imp sourceMember
        (imp orderFormula.encode (imp bijectionFormula.encode selectedCut.encode)))) :=
  certificate_correct selected_cut_graph_transport

end PASoundness.PAtoCompactSelectedCutGraphTransport

#print axioms PASoundness.PAtoCompactSelectedCutGraphTransport.selected_cut_graph_transport
#print axioms PASoundness.PAtoCompactSelectedCutGraphTransport.selected_cut_graph_transport_certificate
