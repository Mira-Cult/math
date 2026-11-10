import PASoundness.PAtoCompactFilterInstantiation
import PASoundness.PAtoCompactRestrictionPredicateRename
import PASoundness.PAtoCompactRestrictionEndpointIntro
import PASoundness.PAtoCompactGraphContextElim
import PASoundness.PAtoCompactGraphVacuity19
import PASoundness.PAtoCompactKuratowskiFresh

/-! K proof that an existing graph edge with endpoints in the chosen sets is
retained by a supplied endpoint filter. No graph existence or quotient is
assumed by this interface. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictionEdgeRetain
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactGraphRestriction
open PASoundness.PAtoCompactFilterInstantiation PASoundness.PAtoCompactRestrictionPredicateRename
open PASoundness.PAtoCompactRestrictionEndpointIntro PASoundness.PAtoCompactGraphWitnessRules
open PASoundness.PAtoCompactGraphContextElim PASoundness.PAtoCompactGraphVacuity19

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Under a supplied exact restriction filter, an existing graph edge is
retained when its two endpoints belong to the displayed sets. The filter's
vacuity at graph-witness name 19 is an explicit finite K derivation input.
All listed syntactic freshness conditions are hypotheses; in particular no
existence of a globally fresh graph or of an order isomorphism is inferred. -/
def retain_edge (g h t x y u v : Nat)
    (htg : t ≠ g) (hth : t ≠ h) (ht19 : t ≠ 19)
    (htx : t ≠ x) (hty : t ≠ y)
    (ht20 : t ≠ 20) (ht21 : t ≠ 21) (ht22 : t ≠ 22)
    (ht25 : t ≠ 25) (ht26 : t ≠ 26)
    (hx19 : 19 ≠ x) (hy19 : 19 ≠ y) (hu19 : 19 ≠ u) (hv19 : 19 ≠ v)
    (fresh : ∀ z ∈ [19,x,y,u,v], z ∉ ({20,21,22,25,26} : Finset Nat))
    (filterVacuity : KDerivation
      (imp (filterGraph g h t (edgePredicate t x y).encode)
        (allCode 19 (filterGraph g h t (edgePredicate t x y).encode)))) :
    KDerivation (imp (filterGraph g h t (edgePredicate t x y).encode)
      (imp (member x u) (imp (member y v)
        (imp (graphFormula g u v).encode (graphFormula h u v).encode)))) := by
  let P := edgePredicate t x y
  let F := filterGraph g h t P.encode
  let X := member x u
  let Y := member y v
  let W := both (member g 19) (pairFormula 19 u v).encode
  let T := graphFormula h u v
  let Γ := [Y,X,F]
  have hp : P.binders = ({20,21,22,25,26} : Finset Nat) := by
    simp [P, edgePredicate, namedBoth, Formula.binders,
      PAtoCompactKuratowskiFresh.pair_binders]
    decide
  have ht : t ∉ P.binders := by rw [hp]; simp [ht20, ht21, ht22, ht25, ht26]
  have h19 : 19 ∉ P.binders := by rw [hp]; decide
  have hvacuity : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 19 q)) := by
    intro q hq
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hq
    by_cases hY : q = Y
    · subst q
      exact membershipVacuity y v 19 hy19 hv19
    by_cases hX : q = X
    · subst q
      exact membershipVacuity x u 19 hx19 hu19
    have hF : q = F := (hq.resolve_left hY).resolve_left hX
    subst q
    exact filterVacuity
  have hstep : Context Γ (imp W T.encode) := by
    apply Context.deduction
    have hw : Context (W :: Γ) W := Context.head Γ W
    have hf : Context (W :: Γ) F := .hypothesis (by simp [Γ])
    have hx : Context (W :: Γ) X := .hypothesis (by simp [Γ])
    have hy : Context (W :: Γ) Y := .hypothesis (by simp [Γ])
    have hg : Context (W :: Γ) (member g 19) := Context.conjunctionLeft hw
    have hpair : Context (W :: Γ) (pairFormula 19 u v).encode := Context.conjunctionRight hw
    have hpred : Context (W :: Γ) (edgePredicate 19 x y).encode :=
      .mp hpair (.mp hy (.mp hx (.closed (endpoint_intro 19 x y u v fresh))))
    have hat := filter_at g h t 19 P htg hth ht19 ht h19
    rw [rename_edge_to_graph_witness t x y htx hty ht20 ht21 ht22 ht25 ht26] at hat
    have hiff : Context (W :: Γ)
        (both (imp (member h 19) (both (member g 19) (edgePredicate 19 x y).encode))
          (imp (both (member g 19) (edgePredicate 19 x y).encode) (member h 19))) :=
      .mp hf (.closed hat)
    have hh : Context (W :: Γ) (member h 19) :=
      .mp (Context.conjunctionIntro hg hpred) (Context.conjunctionRight hiff)
    exact .mp (Context.conjunctionIntro hh hpair) (.closed (graph_intro h u v))
  have hedge : Context Γ (imp (graphFormula g u v).encode T.encode) :=
    graph_context_imp Γ g u v T hvacuity (graph_vacuity_19 h u v) hstep
  exact Context.closeEmpty (Context.deduction (Context.deduction (Context.deduction hedge)))

/-- The finite derivation above has its exact producer-checkable certificate. -/
theorem retain_edge_certificate (g h t x y u v : Nat)
    (htg : t ≠ g) (hth : t ≠ h) (ht19 : t ≠ 19)
    (htx : t ≠ x) (hty : t ≠ y)
    (ht20 : t ≠ 20) (ht21 : t ≠ 21) (ht22 : t ≠ 22)
    (ht25 : t ≠ 25) (ht26 : t ≠ 26)
    (hx19 : 19 ≠ x) (hy19 : 19 ≠ y) (hu19 : 19 ≠ u) (hv19 : 19 ≠ v)
    (fresh : ∀ z ∈ [19,x,y,u,v], z ∉ ({20,21,22,25,26} : Finset Nat))
    (filterVacuity : KDerivation
      (imp (filterGraph g h t (edgePredicate t x y).encode)
        (allCode 19 (filterGraph g h t (edgePredicate t x y).encode)))) :
    theoremCode (certificate (retain_edge g h t x y u v htg hth ht19 htx hty
      ht20 ht21 ht22 ht25 ht26 hx19 hy19 hu19 hv19 fresh filterVacuity)) =
      imp (filterGraph g h t (edgePredicate t x y).encode)
        (imp (member x u) (imp (member y v)
          (imp (graphFormula g u v).encode (graphFormula h u v).encode))) :=
  certificate_correct (retain_edge g h t x y u v htg hth ht19 htx hty
    ht20 ht21 ht22 ht25 ht26 hx19 hy19 hu19 hv19 fresh filterVacuity)

end PASoundness.PAtoCompactRestrictionEdgeRetain

#print axioms PASoundness.PAtoCompactRestrictionEdgeRetain.retain_edge
#print axioms PASoundness.PAtoCompactRestrictionEdgeRetain.retain_edge_certificate
