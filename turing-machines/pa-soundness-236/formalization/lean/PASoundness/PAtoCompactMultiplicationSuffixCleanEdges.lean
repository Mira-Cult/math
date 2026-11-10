import PASoundness.PAtoCompactRestrictionEndpointElimClosed

/-! Endpoint extraction from a supplied clean suffix graph. Graph 6 is clean
with source 31 and suffix 40. This does not assert graph existence or that a
raw bijection has no garbage. -/
namespace PASoundness.PAtoCompactMultiplicationSuffixCleanEdges
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactGraphRestriction
open PASoundness.PAtoCompactRestrictionEndpointElimClosed
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Every stored edge has source in 31 and target in 40. -/
def suffixClean : Formula := .all 19 (.imp (.member 6 19) (edgePredicate 19 31 40))

/-- A queried edge of the supplied clean graph has both intended endpoints.
The explicit distinctness condition is syntactic; its objects may coincide. -/
def clean_endpoints (u v : Nat)
    (pairFresh : [19,25,26,u,v,20,21,22,23,24].Nodup) :
    KDerivation (imp suffixClean.encode (imp (graphFormula 6 u v).encode
      (both (member 31 u) (member 40 v)))) := by
  have h19u : 19 ≠ u := by intro h; subst u; simp at pairFresh
  have h19v : 19 ≠ v := by intro h; subst v; simp at pairFresh
  let M := member 6 19
  let P := (pairFormula 19 u v).encode
  let R := (edgePredicate 19 31 40).encode
  let T := both (member 31 u) (member 40 v)
  let A := both M P
  have hEP : KDerivation (imp P (imp R T)) :=
    endpoints_from_predicate 31 40 u v pairFresh (by decide) (by decide) (by decide) (by decide)
  have hlocal : KDerivation (imp (imp M R) (imp A T)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [A,imp M R]
    have ha : Context Γ A := .head _ _
    have hr : Context Γ (imp M R) := .hypothesis (by simp [Γ])
    exact .mp (.mp (Context.conjunctionLeft ha) hr)
      (.mp (Context.conjunctionRight ha) (.closed hEP))
  let f : Formula := namedBoth (.member 31 u) (.member 40 v)
  have hfv : 19 ∉ f.names := by
    simp [f, namedBoth, Formula.names, h19u,h19v]
  have hv : KDerivation (imp T (allCode 19 T)) := by
    have h := f.vacuity 19 hfv
    simpa [f,T,namedBoth,Formula.encode,CompactProof.both,CompactProof.neg] using h
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 6 u v).encode,suffixClean.encode]
  have hg : Context Γ (existsCode 19 A) := .head _ _
  have hc : Context Γ (allCode 19 (imp M R)) := by
    exact Context.under (Context.head [] suffixClean.encode) _
  have hall : Context Γ (allCode 19 (imp A T)) := Context.allMP hc (.closed (.generalize 19 hlocal))
  exact Context.existsElim hv hall hg

/-- Both point queries supply the four source/target memberships used by the
same-row lexicographic comparison. -/
def two_edges_endpoints : KDerivation (imp suffixClean.encode
    (imp (graphFormula 6 4 5).encode (imp (graphFormula 6 8 9).encode
      (both (both (member 31 4) (member 40 5))
        (both (member 31 8) (member 40 9)))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 6 8 9).encode,(graphFormula 6 4 5).encode,suffixClean.encode]
  have h2 : Context Γ (graphFormula 6 8 9).encode := .head _ _
  have h1 : Context Γ (graphFormula 6 4 5).encode := .hypothesis (by simp [Γ])
  have hc : Context Γ suffixClean.encode := .hypothesis (by simp [Γ])
  exact Context.conjunctionIntro
    (.mp h1 (.mp hc (.closed (clean_endpoints 4 5 (by decide)))))
    (.mp h2 (.mp hc (.closed (clean_endpoints 8 9 (by decide)))))

theorem two_edges_endpoints_certificate : theoremCode (certificate two_edges_endpoints) =
    imp suffixClean.encode (imp (graphFormula 6 4 5).encode (imp (graphFormula 6 8 9).encode
      (both (both (member 31 4) (member 40 5))
        (both (member 31 8) (member 40 9))))) := certificate_correct two_edges_endpoints
end PASoundness.PAtoCompactMultiplicationSuffixCleanEdges
#print axioms PASoundness.PAtoCompactMultiplicationSuffixCleanEdges.clean_endpoints
#print axioms PASoundness.PAtoCompactMultiplicationSuffixCleanEdges.two_edges_endpoints
#print axioms PASoundness.PAtoCompactMultiplicationSuffixCleanEdges.two_edges_endpoints_certificate
