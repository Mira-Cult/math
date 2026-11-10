import PASoundness.PAtoCompactRestrictionEdgeRetain
import PASoundness.PAtoCompactRestrictionFilterVacuity
import PASoundness.PAtoCompactRestrictionFresh19

/-! Concrete fresh-name specialization of K graph-edge retention. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictionEdgeRetainClosed
open PASoundness.CompactProof PASoundness.CompactNamed
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactGraphRestriction PASoundness.PAtoCompactRestrictionFilterVacuity

/-- Under these explicit pairwise-distinct labels, the endpoint filter
retains every supplied source edge with endpoints in the indicated sets.
The filtered graph is a premise; its existence and isomorphism properties
are separate. Distinct labels may still denote equal objects. -/
def retain_edge (g h t x y u v : Nat)
    (fresh : [g,h,t,x,y,u,v,19,20,21,22,25,26].Nodup) :
    KDerivation (imp (filterGraph g h t (edgePredicate t x y).encode)
      (imp (member x u) (imp (member y v)
        (imp (graphFormula g u v).encode (graphFormula h u v).encode)))) := by
  have htg : t ≠ g := by intro he; subst t; simp at fresh
  have hth : t ≠ h := by intro he; subst t; simp at fresh
  have ht19 : t ≠ 19 := by intro he; subst t; simp at fresh
  have htx : t ≠ x := by intro he; subst t; simp at fresh
  have hty : t ≠ y := by intro he; subst t; simp at fresh
  have ht20 : t ≠ 20 := by intro he; subst t; simp at fresh
  have ht21 : t ≠ 21 := by intro he; subst t; simp at fresh
  have ht22 : t ≠ 22 := by intro he; subst t; simp at fresh
  have ht25 : t ≠ 25 := by intro he; subst t; simp at fresh
  have ht26 : t ≠ 26 := by intro he; subst t; simp at fresh
  have hx19 : 19 ≠ x := by intro he; subst x; simp at fresh
  have hy19 : 19 ≠ y := by intro he; subst y; simp at fresh
  have hu19 : 19 ≠ u := by intro he; subst u; simp at fresh
  have hv19 : 19 ≠ v := by intro he; subst v; simp at fresh
  have hfresh : ∀ z ∈ [19,x,y,u,v], z ∉ ({20,21,22,25,26} : Finset Nat) := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl <;> simp_all
  have hsub : List.Sublist [g,h,t,x,y,19,20,21,22,25,26]
      [g,h,t,x,y,u,v,19,20,21,22,25,26] := by simp
  have hfilter : 19 ∉ (namedFilter g h t x y).names :=
    PAtoCompactRestrictionFresh19.filter_fresh_19 g h t x y (fresh.sublist hsub)
  exact PAtoCompactRestrictionEdgeRetain.retain_edge g h t x y u v htg hth ht19
    htx hty ht20 ht21 ht22 ht25 ht26 hx19 hy19 hu19 hv19 hfresh
    (restriction_filter_vacuity g h t x y 19 hfilter)

theorem retain_edge_certificate (g h t x y u v : Nat)
    (fresh : [g,h,t,x,y,u,v,19,20,21,22,25,26].Nodup) :
    theoremCode (certificate (retain_edge g h t x y u v fresh)) =
      imp (filterGraph g h t (edgePredicate t x y).encode)
        (imp (member x u) (imp (member y v)
          (imp (graphFormula g u v).encode (graphFormula h u v).encode))) :=
  certificate_correct (retain_edge g h t x y u v fresh)

end PASoundness.PAtoCompactRestrictionEdgeRetainClosed

#print axioms PASoundness.PAtoCompactRestrictionEdgeRetainClosed.retain_edge
#print axioms PASoundness.PAtoCompactRestrictionEdgeRetainClosed.retain_edge_certificate
