import PASoundness.PAtoCompactSuffixGuardedForwardUpgrade
import PASoundness.PAtoCompactRestrictionEndpointElimClosed

/-! Stored-pair cleanliness implies source-guarded graph cleanliness. This
finite K derivation assumes the supplied graph is clean; it does not construct
the graph or assert a candidate property of the suffix. -/
namespace PASoundness.PAtoCompactSuffixCleanGraphGuard

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactGraphRestriction PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactRestrictionEndpointElimClosed
open PASoundness.PAtoCompactSuffixGuardedForwardUpgrade

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def storedClean : Formula := .all 19 (.imp (.member 6 19) (edgePredicate 19 1 31))

/-- A queried edge has its target in the suffix; its pair coordinates are
extracted inside K from the supplied stored-pair cleanliness. -/
def clean_target_point : KDerivation (imp storedClean.encode
    (imp (graphFormula 6 2 4).encode (member 31 4))) := by
  let M := member 6 19
  let P := (pairFormula 19 2 4).encode
  let R := (edgePredicate 19 1 31).encode
  let T := member 31 4
  let A := both M P
  have hEP : KDerivation (imp P (imp R (both (member 1 2) T))) :=
    endpoints_from_predicate 1 31 2 4 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hlocal : KDerivation (imp (imp M R) (imp A T)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [A,imp M R]
    have ha : Context Γ A := .head _ _
    have hr : Context Γ (imp M R) := .hypothesis (by simp [Γ])
    have hends : Context Γ (both (member 1 2) T) :=
      .mp (.mp (Context.conjunctionLeft ha) hr)
        (.mp (Context.conjunctionRight ha) (.closed hEP))
    exact Context.conjunctionRight hends
  let f : Formula := .member 31 4
  have hv : KDerivation (imp T (allCode 19 T)) := by
    have h := f.vacuity 19 (by decide)
    simpa [f,T,Formula.encode] using h
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 6 2 4).encode,storedClean.encode]
  have hg : Context Γ (existsCode 19 A) := .head _ _
  have hc : Context Γ (allCode 19 (imp M R)) := by
    exact Context.under (Context.head [] storedClean.encode) _
  have hall : Context Γ (allCode 19 (imp A T)) :=
    Context.allMP hc (.closed (.generalize 19 hlocal))
  exact Context.existsElim hv hall hg

/-- Stored-pair cleanliness implies the weaker source-guarded condition. -/
def stored_clean_graph_guard : KDerivation (imp storedClean.encode graphClean.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [storedClean.encode]
  let body : Formula := .imp (.member 1 2) (.imp (graphFormula 6 2 4) (.member 31 4))
  have hpoint : Context Γ body.encode := by
    apply Context.deduction
    apply Context.deduction
    let Δ := [(graphFormula 6 2 4).encode,member 1 2,storedClean.encode]
    have he : Context Δ (graphFormula 6 2 4).encode := .head _ _
    have hc : Context Δ storedClean.encode := .hypothesis (by simp [Δ])
    exact .mp he (.mp hc (.closed clean_target_point))
  have hv4 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 4 h)) := by
    intro h hh
    have he : h = storedClean.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 4 storedClean (by decide)
  have hv2 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 2 h)) := by
    intro h hh
    have he : h = storedClean.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 2 storedClean (by decide)
  have hall := Context.generalize 2 hv2 (Context.generalize 4 hv4 hpoint)
  simpa only [graphClean,body,Formula.encode] using hall

theorem stored_clean_graph_guard_certificate : theoremCode (certificate stored_clean_graph_guard) =
    imp storedClean.encode graphClean.encode := certificate_correct stored_clean_graph_guard

end PASoundness.PAtoCompactSuffixCleanGraphGuard

#print axioms PASoundness.PAtoCompactSuffixCleanGraphGuard.storedClean
#print axioms PASoundness.PAtoCompactSuffixCleanGraphGuard.clean_target_point
#print axioms PASoundness.PAtoCompactSuffixCleanGraphGuard.stored_clean_graph_guard
#print axioms PASoundness.PAtoCompactSuffixCleanGraphGuard.stored_clean_graph_guard_certificate
