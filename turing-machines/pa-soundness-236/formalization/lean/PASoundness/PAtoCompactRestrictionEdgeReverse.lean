import PASoundness.PAtoCompactRestrictionSubset
import PASoundness.PAtoCompactGraphContextElim

/-! Every edge of a filtered graph was already an edge of its source.
The witness-label vacuity derivations are explicit K proof inputs. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictionEdgeReverse
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactGraphWitnessRules PASoundness.PAtoCompactGraphContextElim
open PASoundness.PAtoCompactRestrictionSubset
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Given the filter, a restricted edge implies the same original edge.
The filter test name must differ from graph names and pair-witness 19. The
two displayed vacuity inputs are literal K derivations, so no freshness of
the graph existential or of the encoded predicate is silently assumed.
This direction does not establish that either endpoint lies in a domain. -/
def restricted_edge_source (g h t P u v : Nat)
    (ht19 : t ≠ 19) (hth : t ≠ h) (htg : t ≠ g)
    (filterVacuity : KDerivation
      (imp (filterGraph g h t P) (allCode 19 (filterGraph g h t P))))
    (targetVacuity : KDerivation
      (imp (graphFormula g u v).encode (allCode 19 (graphFormula g u v).encode))) :
    KDerivation (imp (filterGraph g h t P)
      (imp (graphFormula h u v).encode (graphFormula g u v).encode)) := by
  let F := filterGraph g h t P
  let W := both (member h 19) (pairFormula 19 u v).encode
  let T := graphFormula g u v
  let Γ := [F]
  have hv : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 19 q)) := by
    intro q hq
    have hq' : q = F := by simpa [Γ] using hq
    subst q
    exact filterVacuity
  have hs : Context Γ (imp W T.encode) := by
    apply Context.deduction
    have hw : Context (W :: Γ) W := Context.head Γ W
    have hf : Context (W :: Γ) F := .hypothesis (by simp [Γ])
    have hm : Context (W :: Γ) (member h 19) := Context.conjunctionLeft hw
    have hp : Context (W :: Γ) (pairFormula 19 u v).encode := Context.conjunctionRight hw
    have hg : Context (W :: Γ) (member g 19) :=
      .mp hm (.mp hf (.closed (filter_member_source g h t P 19 ht19 hth htg)))
    exact .mp (Context.conjunctionIntro hg hp) (.closed (graph_intro g u v))
  have he : Context Γ (imp (graphFormula h u v).encode T.encode) :=
    graph_context_imp Γ h u v T hv targetVacuity hs
  exact Context.closeEmpty (Context.deduction he)

/-- The exposed derivation has the corresponding checkable compact-code
certificate. It is a certificate of the displayed implication, not a new
existence, quotient or arithmetic-interpretation theorem. -/
theorem restricted_edge_source_certificate (g h t P u v : Nat)
    (ht19 : t ≠ 19) (hth : t ≠ h) (htg : t ≠ g)
    (filterVacuity : KDerivation
      (imp (filterGraph g h t P) (allCode 19 (filterGraph g h t P))))
    (targetVacuity : KDerivation
      (imp (graphFormula g u v).encode (allCode 19 (graphFormula g u v).encode))) :
    theoremCode (certificate (restricted_edge_source g h t P u v ht19 hth htg
      filterVacuity targetVacuity)) =
      imp (filterGraph g h t P)
        (imp (graphFormula h u v).encode (graphFormula g u v).encode) :=
  certificate_correct (restricted_edge_source g h t P u v ht19 hth htg
    filterVacuity targetVacuity)

end PASoundness.PAtoCompactRestrictionEdgeReverse

#print axioms PASoundness.PAtoCompactRestrictionEdgeReverse.restricted_edge_source
#print axioms PASoundness.PAtoCompactRestrictionEdgeReverse.restricted_edge_source_certificate
