import PASoundness.PAtoCompactRestrictionPredicateAt19
import PASoundness.PAtoCompactRestrictionEndpointElimClosed
import PASoundness.PAtoCompactRestrictionFilterVacuity
import PASoundness.PAtoCompactRestrictionFresh19
import PASoundness.PAtoCompactGraphContextElim

/-! Endpoint membership for an edge of the displayed restricted graph. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictionGraphEndpoints
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactGraphRestriction PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactRestrictionFilterVacuity PASoundness.PAtoCompactGraphContextElim
open PASoundness.PAtoCompactRestrictionEndpointVacuity
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The exact filtered graph has no edge whose endpoints lie outside the two
displayed endpoint sets. The two freshness lists concern syntactic labels,
not object inequality; x may equal u and y may equal v as labels. This
finite K derivation asserts no graph coverage or quotient injectivity. -/
def restricted_edge_endpoints (g h t x y u v : Nat)
    (filterFresh : [g,h,t,x,y,19,20,21,22,25,26].Nodup)
    (pairFresh : [19,25,26,u,v,20,21,22,23,24].Nodup) :
    KDerivation (imp (filterGraph g h t (edgePredicate t x y).encode)
      (imp (graphFormula h u v).encode (both (member x u) (member y v)))) := by
  have h19x : 19 ≠ x := by intro he; subst x; simp at filterFresh
  have h19y : 19 ≠ y := by intro he; subst y; simp at filterFresh
  have h19u : 19 ≠ u := by intro he; subst u; simp at pairFresh
  have h19v : 19 ≠ v := by intro he; subst v; simp at pairFresh
  have h25x : 25 ≠ x := by intro he; subst x; simp at filterFresh
  have h26x : 26 ≠ x := by intro he; subst x; simp at filterFresh
  have h25y : 25 ≠ y := by intro he; subst y; simp at filterFresh
  have h26y : 26 ≠ y := by intro he; subst y; simp at filterFresh
  let F := filterGraph g h t (edgePredicate t x y).encode
  let W := both (member h 19) (pairFormula 19 u v).encode
  let T := namedBoth (.member x u) (.member y v)
  let Γ := [F]
  have hvF : KDerivation (imp F (allCode 19 F)) :=
    restriction_filter_vacuity g h t x y 19
      (PAtoCompactRestrictionFresh19.filter_fresh_19 g h t x y filterFresh)
  have hvΓ : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 19 q)) := by
    intro q hq
    have he : q = F := by simpa [Γ] using hq
    subst q
    exact hvF
  have hvT : KDerivation (imp T.encode (allCode 19 T.encode)) := by
    simpa [T, namedBoth, Formula.encode, CompactProof.both, CompactProof.neg] using
      endpoints_vacuity x y u v 19 h19x h19y h19u h19v
  have hs : Context Γ (imp W T.encode) := by
    apply Context.deduction
    have hw : Context (W :: Γ) W := .head _ _
    have hf : Context (W :: Γ) F := .hypothesis (by simp [Γ])
    have hm : Context (W :: Γ) (member h 19) := Context.conjunctionLeft hw
    have hp : Context (W :: Γ) (pairFormula 19 u v).encode := Context.conjunctionRight hw
    have he : Context (W :: Γ) (edgePredicate 19 x y).encode :=
      .mp hm (.mp hf (.closed
        (PAtoCompactRestrictionPredicateAt19.filter_member_predicate g h t x y filterFresh)))
    have hend := PAtoCompactRestrictionEndpointElimClosed.endpoints_from_predicate
      x y u v pairFresh h25x h26x h25y h26y
    simpa [T, namedBoth, Formula.encode, CompactProof.both, CompactProof.neg] using
      (Context.mp he (Context.mp hp (.closed hend)))
  have hresult : Context Γ (imp (graphFormula h u v).encode T.encode) :=
    graph_context_imp Γ h u v T hvΓ hvT hs
  exact Context.closeEmpty (Context.deduction hresult)

theorem restricted_edge_endpoints_certificate (g h t x y u v : Nat)
    (filterFresh : [g,h,t,x,y,19,20,21,22,25,26].Nodup)
    (pairFresh : [19,25,26,u,v,20,21,22,23,24].Nodup) :
    theoremCode (certificate (restricted_edge_endpoints g h t x y u v filterFresh pairFresh)) =
      imp (filterGraph g h t (edgePredicate t x y).encode)
        (imp (graphFormula h u v).encode (both (member x u) (member y v))) :=
  certificate_correct (restricted_edge_endpoints g h t x y u v filterFresh pairFresh)

end PASoundness.PAtoCompactRestrictionGraphEndpoints

#print axioms PASoundness.PAtoCompactRestrictionGraphEndpoints.restricted_edge_endpoints
