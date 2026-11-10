import PASoundness.PAtoCompactSuccCongruenceData

/-! Conditional top-source target uniqueness in literal K. A supplied
clean-graph endpoint derivation and the explicit new-edge split are retained;
the contradiction uses only encoded negation into code 1. No semantic
soundness, graph collection, or successor congruence is asserted here. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccTopUnique
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactSuccCongruenceData

/-- Pointwise split of a new edge from the top source. -/
def topEdgeSplit : Nat := imp (graphFormula 9 0 4).encode
  (either (graphFormula 6 0 4).encode (both (equal 0 0) (equal 4 1)))

/-- Clean old graphs have no edge at the top source when that source does not
belong to itself. The source endpoint derivation is an explicit proof-data
premise; no ordinary semantic reading of code 1 is assumed. -/
def top_unique_of_endpoint
    (hEndpoint : KDerivation (imp cleanGraph
      (imp (graphFormula 6 0 4).encode (member 0 0)))) :
    KDerivation (imp cleanGraph (imp sourceIrreflexive
      (imp topEdgeSplit (imp (graphFormula 9 0 4).encode (equal 4 1))))) := by
  let C := cleanGraph
  let N := sourceIrreflexive
  let S := topEdgeSplit
  let G := (graphFormula 9 0 4).encode
  let O := (graphFormula 6 0 4).encode
  let P := both (equal 0 0) (equal 4 1)
  let Γ := [G,S,N,C]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have hn : Context Γ N := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hg : Context Γ G := Context.head _ _
  have hcases : Context Γ (either O P) := .mp hg hs
  apply Context.disjunctionElim hcases
  · have ho : Context (O :: Γ) O := Context.head Γ O
    have hm : Context (O :: Γ) (member 0 0) :=
      .mp ho (.mp (Context.under hc O) (.closed hEndpoint))
    have hfalse : Context (O :: Γ) 1 := .mp hm (Context.under hn O)
    exact Context.explode (equal 4 1) hfalse
  · exact Context.conjunctionRight (Context.head Γ P)

theorem top_unique_of_endpoint_certificate
    (hEndpoint : KDerivation (imp cleanGraph
      (imp (graphFormula 6 0 4).encode (member 0 0)))) :
    theoremCode (certificate (top_unique_of_endpoint hEndpoint)) =
      imp cleanGraph (imp sourceIrreflexive
        (imp topEdgeSplit (imp (graphFormula 9 0 4).encode (equal 4 1)))) :=
  certificate_correct (top_unique_of_endpoint hEndpoint)

end PASoundness.PAtoCompactSuccTopUnique

#print axioms PASoundness.PAtoCompactSuccTopUnique.top_unique_of_endpoint
#print axioms PASoundness.PAtoCompactSuccTopUnique.top_unique_of_endpoint_certificate
