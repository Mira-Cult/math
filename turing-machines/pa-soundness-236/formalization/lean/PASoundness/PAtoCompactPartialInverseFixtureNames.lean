import PASoundness.PAtoCompactPartialInversePredicate
import PASoundness.PAtoCompactQuantifiedRefutation
import PASoundness.PAtoCompactAdjunction

/-! Explicit syntax-name checks for one partial-inverse induction instance.
These do not establish the induction step or an inverse-graph theorem. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseFixtureNames
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactCounterexampleSet PASoundness.PAtoCompactUniformBase
open PASoundness.PAtoCompactUniformStep PASoundness.PAtoCompactQuantifiedRefutation
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactPartialInversePredicate

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def filterName : Nat := filterPredicate 31 30 (neg predicate.encode)

/-- A general symbolic lower bound that does not evaluate the encoded formula. -/
theorem member_lt_filter (x t P : Nat) : member x t < filterPredicate x t P := by
  have h4 := Cantor.left_le_pair (member x t) (neg P)
  have h6 := Cantor.left_le_pair (imp (member x t) (neg P)) 1
  have hm : 0 < member x t := by unfold member; omega
  unfold filterPredicate both neg imp at *
  omega

theorem filter_large : 100 < filterName := by
  have h := Cantor.left_le_pair 31 30
  have hm : 100 < member 31 30 := by unfold member; omega
  exact Nat.lt_trans hm (member_lt_filter 31 30 (neg predicate.encode))

theorem chosen_successor_fresh :
    [8,31,42,37,32,33,43,44,45,34,30,10,36,46,35,47,48,49,51,50].Nodup := by decide
theorem fresh_nonempty : [31,34,30,35,10,36,8].Nodup := by decide
theorem fresh_induction : [31,30,8,34,10,36].Nodup := by decide
theorem fresh_domain : [10,32,33,38,30,8,39,15].Nodup := by decide
theorem fresh_outer : [31,10,32,33,37,40,30,8,39,38,41].Nodup := by decide
theorem fresh_alpha : [31,34,30,10,36,40,8,39].Nodup := by decide

theorem selector_guards : 42 ≠ adjunctionPredicate 8 50 ∧ 31 ≠ adjunctionPredicate 8 50 := by
  have h := (predicate_names_lt 8 50).2
  omega

theorem predicate_aux_fresh : 10 ∉ predicate.names ∧ 8 ∉ predicate.names := by decide

theorem filter_avoids_aux : filterName ∉ [8,34,10,36] ∧ 8 ≠ filterName ∧ 36 ≠ filterName := by
  have hf := filter_large
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  omega

theorem filter_avoids_predicate : filterName ∉ predicate.names := by
  rw [predicate_names]
  have hf := filter_large
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  omega

theorem instance_names : (replace 30 8 predicate).names = {0,1,2,3,6,7,8,19,20,21,22} := by decide
theorem ten_instance_names : (replace 30 10 predicate).names = {0,1,2,3,6,7,10,19,20,21,22} := by decide

theorem graph_aux_fresh : 10 ∉ (namedFilterGraph 31 30 predicate).names := by
  have hf := filter_large
  change 100 < filterPredicate 31 30 (neg predicate.encode) at hf
  simp only [namedFilterGraph, namedCounterexampleGraphBody, namedBoth, Formula.not,
    Formula.names, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton,
    Finset.notMem_empty, not_false_eq_true, not_or, predicate_names, and_true]
  omega

theorem filter_base_fresh : filterName ∉ (namedAllBase 30 10 9 predicate).names := by
  have hf := filter_large
  simp only [namedAllBase, namedUniformBaseBody, Formula.names, Finset.mem_insert,
    Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty, not_false_eq_true, not_or,
    ten_instance_names, and_true]
  omega

theorem filter_step_fresh : filterName ∉ (namedAllSteps 31 30 8 10 15 32 33 predicate).names := by
  have hf := filter_large
  simp only [namedAllSteps, namedUniformStepBody, namedPredecessorCore, namedBoth,
    namedSuccessorBody, namedEither, transitiveBody, Formula.names, Finset.mem_insert,
    Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty, not_false_eq_true,
    not_or, instance_names, ten_instance_names, and_true]
  omega

theorem filter_class_fresh : filterName ∉ (namedAllClassification 31 8 10 9 15 32 33).names := by
  have hf := filter_large
  simp only [namedAllClassification, namedPredecessorCore, namedBoth, namedSuccessorBody,
    namedEither, transitiveBody, Formula.names, Finset.mem_insert, Finset.mem_union,
    Finset.mem_singleton, Finset.notMem_empty, not_false_eq_true, not_or, and_true]
  omega

theorem container_base_fresh : 31 ∉ (namedAllBase 30 10 9 predicate).names := by
  simp only [namedAllBase, namedUniformBaseBody, Formula.names, Finset.mem_insert,
    Finset.mem_union, Finset.mem_singleton, not_or, ten_instance_names]
  decide

theorem container_instance_fresh : 31 ∉ (replace 30 8 predicate).names := by
  rw [instance_names]
  decide

end PASoundness.PAtoCompactPartialInverseFixtureNames

#print axioms PASoundness.PAtoCompactPartialInverseFixtureNames.filter_large
#print axioms PASoundness.PAtoCompactPartialInverseFixtureNames.chosen_successor_fresh
