import PASoundness.PAtoCompactSeededSpanSuccessor
import PASoundness.PAtoCompactQuantifiedRefutation
import PASoundness.PAtoCompactAdjunction

/-! Explicit name and selector-freshness checks for the seeded common-source span
candidate-induction instance. These are syntactic side conditions only; they
do not prove the successor step, graph collection or quotient transitivity. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSeededSpanFixtureNames
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactCounterexampleSet PASoundness.PAtoCompactUniformBase
open PASoundness.PAtoCompactUniformStep PASoundness.PAtoCompactQuantifiedRefutation
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactSeededSpanSuccessor
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def predicate : Formula := inductionPredicate

theorem predicate_names : predicate.names =
    {0,1,2,3,4,6,7,8,9,14,19,20,21,22,30} := by decide

theorem induction_name_unbound : 30 ∉ predicate.binders := by decide

theorem instance_name_unbound : 25 ∉ predicate.binders := by decide

def filterName : Nat := filterPredicate 31 30 (neg predicate.encode)

/-- Symbolic selector bound; the (potentially enormous) encoded predicate is
not evaluated. -/
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
    [25,31,42,37,32,33,43,44,45,34,30,13,36,46,35,47,48,49,51,50].Nodup := by decide
theorem fresh_nonempty : [31,34,30,35,13,36,25].Nodup := by decide
theorem fresh_induction : [31,30,25,34,13,36].Nodup := by decide
theorem fresh_domain : [13,32,33,38,30,10,39,15].Nodup := by decide
theorem fresh_outer : [31,13,32,33,37,40,30,10,39,38,41].Nodup := by decide
theorem fresh_alpha : [31,34,30,13,36,40,10,39].Nodup := by decide

theorem selector_guards : 42 ≠ adjunctionPredicate 25 50 ∧ 31 ≠ adjunctionPredicate 25 50 := by
  have h := (predicate_names_lt 25 50).2
  omega

theorem predicate_aux_fresh : 13 ∉ predicate.names ∧ 10 ∉ predicate.names := by decide

theorem filter_avoids_aux : filterName ∉ [25,34,13,36] ∧ 10 ≠ filterName ∧ 36 ≠ filterName := by
  have hf := filter_large
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  omega

theorem filter_avoids_predicate : filterName ∉ predicate.names := by
  rw [predicate_names]
  have hf := filter_large
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  omega

theorem instance_names : (replace 30 25 predicate).names =
    {0,1,2,3,4,6,7,8,9,14,19,20,21,22,25} := by decide

theorem predecessor_instance_names : (replace 30 10 predicate).names =
    {0,1,2,3,4,6,7,8,9,10,14,19,20,21,22} := by decide

theorem successor_instance_names : (replace 30 13 predicate).names =
    {0,1,2,3,4,6,7,8,9,13,14,19,20,21,22} := by decide

theorem graph_aux_fresh : 13 ∉ (namedFilterGraph 31 30 predicate).names := by
  have hf := filter_large
  change 100 < filterPredicate 31 30 (neg predicate.encode) at hf
  simp only [namedFilterGraph, namedCounterexampleGraphBody, namedBoth, Formula.not,
    Formula.names, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton,
    Finset.notMem_empty, not_false_eq_true, not_or, predicate_names, and_true]
  omega

theorem filter_base_fresh : filterName ∉ (namedAllBase 30 13 11 predicate).names := by
  have hf := filter_large
  simp only [namedAllBase, namedUniformBaseBody, Formula.names, Finset.mem_insert,
    Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty, not_false_eq_true, not_or,
    successor_instance_names, and_true]
  omega

theorem filter_step_fresh : filterName ∉ (namedAllSteps 31 30 10 13 15 32 33 predicate).names := by
  have hf := filter_large
  simp only [namedAllSteps, namedUniformStepBody, namedPredecessorCore, namedBoth,
    namedSuccessorBody, namedEither, transitiveBody, Formula.names, Finset.mem_insert,
    Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty, not_false_eq_true,
    not_or, predecessor_instance_names, successor_instance_names, and_true]
  omega

theorem filter_class_fresh : filterName ∉ (namedAllClassification 31 10 13 11 15 32 33).names := by
  have hf := filter_large
  simp only [namedAllClassification, namedPredecessorCore, namedBoth, namedSuccessorBody,
    namedEither, transitiveBody, Formula.names, Finset.mem_insert, Finset.mem_union,
    Finset.mem_singleton, Finset.notMem_empty, not_false_eq_true, not_or, and_true]
  omega

theorem container_base_fresh : 31 ∉ (namedAllBase 30 13 11 predicate).names := by
  simp only [namedAllBase, namedUniformBaseBody, Formula.names, Finset.mem_insert,
    Finset.mem_union, Finset.mem_singleton, not_or, successor_instance_names]
  decide

theorem container_instance_fresh : 31 ∉ (replace 30 25 predicate).names := by
  rw [instance_names]
  decide

end PASoundness.PAtoCompactSeededSpanFixtureNames

#print axioms PASoundness.PAtoCompactSeededSpanFixtureNames.filter_large
#print axioms PASoundness.PAtoCompactSeededSpanFixtureNames.chosen_successor_fresh
