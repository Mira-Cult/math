import PASoundness.PAtoCompactQuantifiedRefutation
import PASoundness.CompactFreshen

/-! Syntactic freshness helpers for the candidate-restricted induction engine.
They eliminate context-name side conditions from explicit distinctness and
absence facts. No K proof or PA induction result is asserted. -/
namespace PASoundness.PAtoCompactInductionContextFreshnessHelpers
open PASoundness.CompactProof PASoundness.CompactNamed
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactQuantifiedRefutation
open PASoundness.PAtoCompactCounterexampleSet PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactUniformBase

/-- A name below the active predicate name and absent from the predicate and
container is absent from the full counterexample filter graph. -/
theorem filter_graph_fresh (Y t m : Nat) (f : Formula)
    (hmY : m ≠ Y) (hmt : m < t) (hmf : m ∉ f.names) :
    m ∉ (namedFilterGraph Y t f).names := by
  have hmc : m ≠ filterPredicate Y t (neg f.encode) := by
    have h := (filterPredicate_bounds Y t (neg f.encode)).2.1
    omega
  have hmt' : m ≠ t := by omega
  simpa [namedFilterGraph, namedCounterexampleGraphBody, namedBoth, Formula.names,
    Formula.not, hmf, hmY, hmt', hmc, Ne.symm hmY, Ne.symm hmt', Ne.symm hmc]

/-- If a container name is absent from the predicate and distinct from the
base quantifier's two displayed names, it is absent from the named base. -/
theorem container_base_fresh (Y t m z : Nat) (f : Formula)
    (hYt : Y ≠ t) (hYm : Y ≠ m) (hYz : Y ≠ z) (hYf : Y ∉ f.names) :
    Y ∉ (namedAllBase t m z f).names := by
  have hr : Y ∉ (replace t m f).names := by
    intro hh
    exact hYf ((replace_names_outside t m Y f hYt hYm).mp hh)
  simpa [namedAllBase, namedUniformBaseBody, Formula.names, hr, hYm, hYz,
    Ne.symm hYm, Ne.symm hYz]

/-- The container is absent from the instantiated conclusion when it is
absent from the predicate and differs from both replacement labels. -/
theorem container_instance_fresh (Y t x : Nat) (f : Formula)
    (hYt : Y ≠ t) (hYx : Y ≠ x) (hYf : Y ∉ f.names) :
    Y ∉ (replace t x f).names := by
  intro hh
  exact hYf ((replace_names_outside t x Y f hYt hYx).mp hh)

end PASoundness.PAtoCompactInductionContextFreshnessHelpers

#print axioms PASoundness.PAtoCompactInductionContextFreshnessHelpers.filter_graph_fresh
#print axioms PASoundness.PAtoCompactInductionContextFreshnessHelpers.container_base_fresh
#print axioms PASoundness.PAtoCompactInductionContextFreshnessHelpers.container_instance_fresh
