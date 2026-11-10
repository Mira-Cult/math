import PASoundness.PAtoCompactRestrictionEndpointElimClosed
import PASoundness.PAtoCompactFilterInstantiation
import PASoundness.PAtoCompactTransitiveClosure

/-! Clean-graph endpoint and top-exclusion facts for the unequal-endpoint
addition-successor construction.  The graph, suffix filter, and their labels
are supplied explicitly; no graph construction, isomorphism, or PA arithmetic
theorem is asserted. Compact code 1 is the literal self-membership formula. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionSuccessorGraphClean
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactGraphRestriction PASoundness.PAtoCompactRestrictionEndpointElimClosed
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactFilterInstantiation
open PASoundness.PAtoCompactTransitiveClosure
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Exact clean old graph, with source 31 and old target suffix 34. Its
encoding is definitionally the `oldClean` of AdditionSuccessorOldOld. -/
def oldClean : Formula := .all 19 (.imp (.member 6 19) (edgePredicate 19 31 34))

def suffix : Nat := filterGraph 32 34 35 (neg (member 33 35))

/-- An edge of the supplied clean old graph has both old endpoints. -/
def clean_endpoints (u v : Nat)
    (pairFresh : [19,25,26,u,v,20,21,22,23,24].Nodup) :
    KDerivation (imp oldClean.encode (imp (graphFormula 6 u v).encode
      (both (member 31 u) (member 34 v)))) := by
  have h19u : 19 ≠ u := by intro h; subst u; simp at pairFresh
  have h19v : 19 ≠ v := by intro h; subst v; simp at pairFresh
  let M := member 6 19
  let P := (pairFormula 19 u v).encode
  let R := (edgePredicate 19 31 34).encode
  let T := both (member 31 u) (member 34 v)
  let A := both M P
  have hEP : KDerivation (imp P (imp R T)) :=
    endpoints_from_predicate 31 34 u v pairFresh (by decide) (by decide) (by decide) (by decide)
  have hlocal : KDerivation (imp (imp M R) (imp A T)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [A,imp M R]
    have ha : Context Γ A := Context.head _ _
    have hr : Context Γ (imp M R) := .hypothesis (by simp [Γ])
    exact .mp (.mp (Context.conjunctionLeft ha) hr)
      (.mp (Context.conjunctionRight ha) (.closed hEP))
  let f : Formula := namedBoth (.member 31 u) (.member 34 v)
  have hfv : 19 ∉ f.names := by
    simp [f, namedBoth, Formula.names, h19u,h19v]
  have hv : KDerivation (imp T (allCode 19 T)) := by
    have h := f.vacuity 19 hfv
    simpa [f,T,namedBoth,Formula.encode,CompactProof.both,CompactProof.neg] using h
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 6 u v).encode,oldClean.encode]
  have hg : Context Γ (existsCode 19 A) := Context.head _ _
  have hc : Context Γ (allCode 19 (imp M R)) := by
    exact Context.under (Context.head [] oldClean.encode) _
  have hall : Context Γ (allCode 19 (imp A T)) := Context.allMP hc (.closed (.generalize 19 hlocal))
  exact Context.existsElim hv hall hg

/-- The old graph cannot have an edge from the newly adjoined source top. -/
def source_top_excluded (v : Nat)
    (pairFresh : [19,25,26,31,v,20,21,22,23,24].Nodup) :
    KDerivation (imp oldClean.encode (imp (graphFormula 6 31 v).encode 1)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 6 31 v).encode,oldClean.encode]
  have he : Context Γ (graphFormula 6 31 v).encode := .head _ _
  have hc : Context Γ oldClean.encode := .under (.head [] _) _
  have hself : Context Γ (member 31 31) :=
    Context.conjunctionLeft (.mp he (.mp hc (.closed (clean_endpoints 31 v pairFresh))))
  exact .mp hself (.closed (self_membership_implies_code_one 31))

/-- A suffix cannot contain the result from which it is filtered. -/
def result_outside_suffix : KDerivation (imp suffix (neg (member 34 32))) := by
  let P : Formula := (Formula.member 33 35).not
  have h := filter_at 32 34 35 32 P (by decide) (by decide) (by decide) (by decide) (by decide)
  have hi : KDerivation (imp suffix
      (both (imp (member 34 32) (both (member 32 32) (neg (member 33 32))))
        (imp (both (member 32 32) (neg (member 33 32))) (member 34 32)))) := by
    simpa [suffix,P,Formula.not,Formula.encode,replace,rename,neg] using h
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 34 32,suffix]
  have hm : Context Γ (member 34 32) := .head _ _
  have hf : Context Γ suffix := .under (.head [] _) _
  have hself : Context Γ (member 32 32) :=
    Context.conjunctionLeft (.mp hm (Context.conjunctionLeft (.mp hf (.closed hi))))
  exact .mp hself (.closed (self_membership_implies_code_one 32))

/-- The old graph cannot reach the newly adjoined target top 32. -/
def target_top_excluded (u : Nat)
    (pairFresh : [19,25,26,u,32,20,21,22,23,24].Nodup) :
    KDerivation (imp suffix (imp oldClean.encode (imp (graphFormula 6 u 32).encode 1))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 6 u 32).encode,oldClean.encode,suffix]
  have he : Context Γ (graphFormula 6 u 32).encode := .head _ _
  have hc : Context Γ oldClean.encode := .hypothesis (by simp [Γ])
  have hf : Context Γ suffix := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 34 32) :=
    Context.conjunctionRight (.mp he (.mp hc (.closed (clean_endpoints u 32 pairFresh))))
  exact .mp hm (.mp hf (.closed result_outside_suffix))

theorem clean_endpoints_certificate (u v : Nat)
    (pairFresh : [19,25,26,u,v,20,21,22,23,24].Nodup) :
    theoremCode (certificate (clean_endpoints u v pairFresh)) =
      imp oldClean.encode (imp (graphFormula 6 u v).encode (both (member 31 u) (member 34 v))) :=
  certificate_correct (clean_endpoints u v pairFresh)

theorem source_top_excluded_certificate (v : Nat)
    (pairFresh : [19,25,26,31,v,20,21,22,23,24].Nodup) :
    theoremCode (certificate (source_top_excluded v pairFresh)) =
      imp oldClean.encode (imp (graphFormula 6 31 v).encode 1) :=
  certificate_correct (source_top_excluded v pairFresh)

theorem target_top_excluded_certificate (u : Nat)
    (pairFresh : [19,25,26,u,32,20,21,22,23,24].Nodup) :
    theoremCode (certificate (target_top_excluded u pairFresh)) =
      imp suffix (imp oldClean.encode (imp (graphFormula 6 u 32).encode 1)) :=
  certificate_correct (target_top_excluded u pairFresh)

end PASoundness.PAtoCompactAdditionSuccessorGraphClean

#print axioms PASoundness.PAtoCompactAdditionSuccessorGraphClean.clean_endpoints
#print axioms PASoundness.PAtoCompactAdditionSuccessorGraphClean.source_top_excluded
#print axioms PASoundness.PAtoCompactAdditionSuccessorGraphClean.result_outside_suffix
#print axioms PASoundness.PAtoCompactAdditionSuccessorGraphClean.target_top_excluded
#print axioms PASoundness.PAtoCompactAdditionSuccessorGraphClean.target_top_excluded_certificate
