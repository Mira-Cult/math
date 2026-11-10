import PASoundness.PAtoCompactProductMatchPartialBase
import PASoundness.PAtoCompactPartialCompositionFixtureNames

/-! Fresh labels and selector bounds for a candidate-induction instance for
partial product-match collection. These are syntactic side conditions only;
they do not prove a successor step or construct a nonempty match graph. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchInductionNames

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactCounterexampleSet PASoundness.PAtoCompactUniformBase
open PASoundness.PAtoCompactUniformStep PASoundness.PAtoCompactQuantifiedRefutation
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactPartialCompositionFixtureNames
open PASoundness.PAtoCompactProductMatchPartialBase

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def filterName : Nat := filterPredicate 71 64 (neg predicate.encode)

/-- The bound concerns syntax only and does not evaluate the encoded
predicate or the selector value. -/
theorem predicate_names_bound : predicate.names ⊆ Finset.range 65 := by decide
theorem instance59_bound : (replace 64 59 predicate).names ⊆ Finset.range 65 := by decide
theorem instance74_bound : (replace 64 74 predicate).names ⊆ Finset.range 75 := by decide
theorem instance70_bound : (replace 64 70 predicate).names ⊆ Finset.range 71 := by decide

theorem filter_large : 100 < filterName := by
  have hp := Cantor.left_le_pair 71 64
  have hm : 100 < member 71 64 := by unfold member; omega
  exact Nat.lt_trans hm (member_lt_filter 71 64 (neg predicate.encode))

theorem chosen_successor_fresh :
    [70,71,84,81,77,78,85,86,87,72,64,59,75,88,73,89,90,91,92,93].Nodup := by decide
theorem fresh_nonempty : [71,72,64,73,59,75,70].Nodup := by decide
theorem fresh_induction : [71,64,70,72,59,75].Nodup := by decide
theorem fresh_domain : [59,77,78,79,64,74,80,76].Nodup := by decide
theorem fresh_outer : [71,59,77,78,81,82,64,74,80,79,83].Nodup := by decide
theorem fresh_alpha : [71,72,64,59,75,82,74,80].Nodup := by decide

theorem selector_guards : 84 ≠ adjunctionPredicate 70 93 ∧ 71 ≠ adjunctionPredicate 70 93 := by
  have h := (predicate_names_lt 70 93).2
  omega

theorem predicate_aux_fresh : 59 ∉ predicate.names ∧ 74 ∉ predicate.names := by decide

theorem filter_avoids_aux : filterName ∉ [70,72,59,75] ∧
    74 ≠ filterName ∧ 75 ≠ filterName := by
  have hf := filter_large
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  omega

theorem filter_avoids_predicate : filterName ∉ predicate.names := by
  intro h
  have hh := predicate_names_bound h
  simp only [Finset.mem_range] at hh
  have hf := filter_large
  omega

theorem graph_aux_fresh : 59 ∉ (namedFilterGraph 71 64 predicate).names := by
  have hf := filter_large
  have hp := predicate_aux_fresh.1
  change 100 < filterPredicate 71 64 (neg predicate.encode) at hf
  simp only [namedFilterGraph, namedCounterexampleGraphBody, namedBoth, Formula.not,
    Formula.names, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton,
    Finset.notMem_empty, not_false_eq_true, not_or, hp, and_true]
  omega

theorem filter_base_fresh : filterName ∉ (namedAllBase 64 59 60 predicate).names := by
  have hf := filter_large
  have hn : filterName ∉ (replace 64 59 predicate).names := by
    intro h
    have hh := instance59_bound h
    simp only [Finset.mem_range] at hh
    omega
  simp only [namedAllBase, namedUniformBaseBody, Formula.names, Finset.mem_insert,
    Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty, not_false_eq_true,
    not_or, hn, and_true]
  omega

theorem filter_step_fresh : filterName ∉ (namedAllSteps 71 64 74 59 76 77 78 predicate).names := by
  have hf := filter_large
  have hn₁ : filterName ∉ (replace 64 59 predicate).names := by
    intro h
    have hh := instance59_bound h
    simp only [Finset.mem_range] at hh
    omega
  have hn₂ : filterName ∉ (replace 64 74 predicate).names := by
    intro h
    have hh := instance74_bound h
    simp only [Finset.mem_range] at hh
    omega
  simp only [namedAllSteps, namedUniformStepBody, namedPredecessorCore, namedBoth,
    namedSuccessorBody, namedEither, transitiveBody, Formula.names, Finset.mem_insert,
    Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty, not_false_eq_true,
    not_or, hn₁, hn₂, and_true]
  omega

theorem filter_class_fresh : filterName ∉ (namedAllClassification 71 74 59 60 76 77 78).names := by
  have hf := filter_large
  simp only [namedAllClassification, namedPredecessorCore, namedBoth, namedSuccessorBody,
    namedEither, transitiveBody, Formula.names, Finset.mem_insert, Finset.mem_union,
    Finset.mem_singleton, Finset.notMem_empty, not_false_eq_true, not_or, and_true]
  omega

theorem container_base_fresh : 71 ∉ (namedAllBase 64 59 60 predicate).names := by decide
theorem container_instance_fresh : 71 ∉ (replace 64 70 predicate).names := by decide

end PASoundness.PAtoCompactProductMatchInductionNames

#print axioms PASoundness.PAtoCompactProductMatchInductionNames.predicate_names_bound
#print axioms PASoundness.PAtoCompactProductMatchInductionNames.filter_large
#print axioms PASoundness.PAtoCompactProductMatchInductionNames.graph_aux_fresh
#print axioms PASoundness.PAtoCompactProductMatchInductionNames.filter_step_fresh
