import PASoundness.PAtoCompactRestrictionEdgeRetainClosed
import PASoundness.PAtoCompactRestrictionEdgeReverseClosed
import PASoundness.PAtoCompactRestrictionFresh19

/-! Exact K edge comparison for a supplied endpoint-restricted graph. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictionEdgeEquivalence
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactGraphRestriction PASoundness.PAtoCompactRestrictionFilterVacuity

/-- Given the literal endpoint filter and endpoints in x,y, K derives both
directions of the edge comparison between source and filtered graph.
The displayed labels are distinct; their denoted objects may coincide.
The theorem neither constructs the filter nor asserts an isomorphism. -/
def restricted_edge_iff (g h t x y u v : Nat)
    (fresh : [g,h,t,x,y,u,v,19,20,21,22,25,26].Nodup) :
    KDerivation (imp (filterGraph g h t (edgePredicate t x y).encode)
      (imp (member x u) (imp (member y v)
        (both (imp (graphFormula g u v).encode (graphFormula h u v).encode)
          (imp (graphFormula h u v).encode (graphFormula g u v).encode))))) := by
  let F := filterGraph g h t (edgePredicate t x y).encode
  let X := member x u
  let Y := member y v
  let G := (graphFormula g u v).encode
  let H := (graphFormula h u v).encode
  have htg : t ≠ g := by intro he; subst t; simp at fresh
  have hth : t ≠ h := by intro he; subst t; simp at fresh
  have ht19 : t ≠ 19 := by intro he; subst t; simp at fresh
  have hsub : List.Sublist [g,h,t,x,y,19,20,21,22,25,26]
      [g,h,t,x,y,u,v,19,20,21,22,25,26] := by simp
  have hfresh : 19 ∉ (namedFilter g h t x y).names :=
    PAtoCompactRestrictionFresh19.filter_fresh_19 g h t x y (fresh.sublist hsub)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [Y,X,F]
  have hy : Context Γ Y := Context.head _ _
  have hx : Context Γ X := .hypothesis (by simp [Γ])
  have hf : Context Γ F := .hypothesis (by simp [Γ])
  have hfwd : Context Γ (imp G H) :=
    .mp hy (.mp hx (.mp hf (.closed
      (PAtoCompactRestrictionEdgeRetainClosed.retain_edge g h t x y u v fresh))))
  have hrev : Context Γ (imp H G) :=
    .mp hf (.closed (PAtoCompactRestrictionEdgeReverseClosed.restricted_edge_source
      g h t x y u v ht19 hth htg hfresh))
  exact Context.conjunctionIntro hfwd hrev

theorem restricted_edge_iff_certificate (g h t x y u v : Nat)
    (fresh : [g,h,t,x,y,u,v,19,20,21,22,25,26].Nodup) :
    theoremCode (certificate (restricted_edge_iff g h t x y u v fresh)) =
      imp (filterGraph g h t (edgePredicate t x y).encode)
        (imp (member x u) (imp (member y v)
          (both (imp (graphFormula g u v).encode (graphFormula h u v).encode)
            (imp (graphFormula h u v).encode (graphFormula g u v).encode)))) :=
  certificate_correct (restricted_edge_iff g h t x y u v fresh)

end PASoundness.PAtoCompactRestrictionEdgeEquivalence

#print axioms PASoundness.PAtoCompactRestrictionEdgeEquivalence.restricted_edge_iff
#print axioms PASoundness.PAtoCompactRestrictionEdgeEquivalence.restricted_edge_iff_certificate
