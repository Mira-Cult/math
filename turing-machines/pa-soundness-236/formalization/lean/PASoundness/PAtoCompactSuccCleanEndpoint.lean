import PASoundness.PAtoCompactRestrictionEndpointElimClosed
import PASoundness.PAtoCompactSuccCongruenceData

/-! Endpoint consequences of the explicitly supplied old-graph cleanliness
hypothesis in the successor-congruence argument. This is literal K proof data;
it neither constructs the graph nor proves an isomorphism or quotient law. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccCleanEndpoint
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactGraphRestriction PASoundness.PAtoCompactSuccCongruenceData
open PASoundness.PAtoCompactRestrictionEndpointElimClosed

/-- A clean graph edge's endpoints lie in the old source and target. The
endpoint labels may equal 0 or 1; only the listed bound labels must be fresh. -/
def clean_endpoints (u v : Nat)
    (pairFresh : [19,25,26,u,v,20,21,22,23,24].Nodup) :
    KDerivation (imp cleanGraph (imp (graphFormula 6 u v).encode
      (both (member 0 u) (member 1 v)))) := by
  have h19u : 19 ≠ u := by intro h; subst u; simp at pairFresh
  have h19v : 19 ≠ v := by intro h; subst v; simp at pairFresh
  let M := member 6 19
  let P := (pairFormula 19 u v).encode
  let R := (edgePredicate 19 0 1).encode
  let T := both (member 0 u) (member 1 v)
  let A := both M P
  have hEP : KDerivation (imp P (imp R T)) :=
    endpoints_from_predicate 0 1 u v pairFresh (by decide) (by decide) (by decide) (by decide)
  have hlocal : KDerivation (imp (imp M R) (imp A T)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [A,imp M R]
    have ha : Context Γ A := Context.head _ _
    have hr : Context Γ (imp M R) := .hypothesis (by simp [Γ])
    have hm : Context Γ M := Context.conjunctionLeft ha
    have hp : Context Γ P := Context.conjunctionRight ha
    exact .mp (.mp hm hr) (.mp hp (.closed hEP))
  let f : CompactNamed.Formula := namedBoth (.member 0 u) (.member 1 v)
  have hfv : 19 ∉ f.names := by
    simp [f, namedBoth, CompactNamed.Formula.names, h19u,h19v]
  have hv : KDerivation (imp T (allCode 19 T)) := by
    have h := f.vacuity 19 hfv
    simpa [f,T,namedBoth,CompactNamed.Formula.encode,CompactProof.both,CompactProof.neg] using h
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 6 u v).encode,cleanGraph]
  have hg : Context Γ (existsCode 19 A) := Context.head _ _
  have hc : Context Γ (allCode 19 (imp M R)) := .hypothesis (by simp [Γ,cleanGraph,M,R])
  have hall : Context Γ (allCode 19 (imp A T)) := Context.allMP hc (.closed (.generalize 19 hlocal))
  exact Context.existsElim hv hall hg

theorem clean_endpoints_certificate (u v : Nat)
    (pairFresh : [19,25,26,u,v,20,21,22,23,24].Nodup) :
    theoremCode (certificate (clean_endpoints u v pairFresh)) =
      imp cleanGraph (imp (graphFormula 6 u v).encode (both (member 0 u) (member 1 v))) :=
  certificate_correct (clean_endpoints u v pairFresh)

/-- The old-source/competitor names used by the successor bijection proof. -/
def clean_edge_24 : KDerivation (imp cleanGraph
    (imp (graphFormula 6 2 4).encode (both (member 0 2) (member 1 4)))) :=
  clean_endpoints 2 4 (by decide)

/-- The target guard needed by old-source uniqueness. -/
def clean_edge_target_24 : KDerivation (imp cleanGraph
    (imp (graphFormula 6 2 4).encode (member 1 4))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 6 2 4).encode,cleanGraph]
  have he : Context Γ (graphFormula 6 2 4).encode := Context.head _ _
  have hc : Context Γ cleanGraph := .hypothesis (by simp [Γ])
  exact Context.conjunctionRight (.mp he (.mp hc (.closed clean_edge_24)))

theorem clean_edge_target_24_certificate : theoremCode (certificate clean_edge_target_24) =
    imp cleanGraph (imp (graphFormula 6 2 4).encode (member 1 4)) :=
  certificate_correct clean_edge_target_24

/-- Even when the source label equals the input-set label, cleanliness proves
that an edge from that source would imply old-source self-membership. -/
def clean_edge_04 : KDerivation (imp cleanGraph
    (imp (graphFormula 6 0 4).encode (member 0 0))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 6 0 4).encode,cleanGraph]
  have he : Context Γ (graphFormula 6 0 4).encode := Context.head _ _
  have hc : Context Γ cleanGraph := .hypothesis (by simp [Γ])
  exact Context.conjunctionLeft (.mp he (.mp hc (.closed (clean_endpoints 0 4 (by decide)))))

theorem clean_edge_04_certificate : theoremCode (certificate clean_edge_04) =
    imp cleanGraph (imp (graphFormula 6 0 4).encode (member 0 0)) :=
  certificate_correct clean_edge_04

end PASoundness.PAtoCompactSuccCleanEndpoint

#print axioms PASoundness.PAtoCompactSuccCleanEndpoint.clean_endpoints
#print axioms PASoundness.PAtoCompactSuccCleanEndpoint.clean_endpoints_certificate
#print axioms PASoundness.PAtoCompactSuccCleanEndpoint.clean_edge_24
#print axioms PASoundness.PAtoCompactSuccCleanEndpoint.clean_edge_target_24
#print axioms PASoundness.PAtoCompactSuccCleanEndpoint.clean_edge_target_24_certificate
#print axioms PASoundness.PAtoCompactSuccCleanEndpoint.clean_edge_04
#print axioms PASoundness.PAtoCompactSuccCleanEndpoint.clean_edge_04_certificate
