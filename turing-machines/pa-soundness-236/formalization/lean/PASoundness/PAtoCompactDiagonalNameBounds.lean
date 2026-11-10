import PASoundness.PAtoCompactDiagonalUniformBase
import PASoundness.PAtoCompactQuantifiedRefutation

/-! Concrete named-syntax freshness checks for the diagonal predicate and the
chosen candidate-induction schema. These are finite AST facts, not a K proof,
identity-graph totality, or a PA interpretation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDiagonalNameBounds
open PASoundness.CompactProof PASoundness.CompactNamed
open PASoundness.PAtoCompactDiagonalUniformBase
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactQuantifiedRefutation
open PASoundness.PAtoCompactCounterexampleSet PASoundness.PAtoCompactZeroSuccessor

theorem predicate_names_bounded : diagonalPredicate.names ⊆ Finset.range 45 := by decide

theorem base_names_bounded :
    (namedAllBase 0 34 12 diagonalPredicate).names ⊆ Finset.range 45 := by decide

theorem steps_names_bounded :
    (namedAllSteps 44 0 33 34 36 37 38 diagonalPredicate).names ⊆ Finset.range 45 := by decide

theorem classification_names_bounded :
    (namedAllClassification 44 33 34 12 36 37 38).names ⊆ Finset.range 45 := by decide

/-- The filter witness name is larger than 44 without expanding the encoded
predicate, which may be a very large natural number. -/
theorem filter_name_gt : 44 < filterPredicate 44 0 (neg diagonalPredicate.encode) :=
  (filterPredicate_bounds 44 0 (neg diagonalPredicate.encode)).1

theorem filter_avoids_auxiliaries :
    filterPredicate 44 0 (neg diagonalPredicate.encode) ∉ [30,32,34,35] ∧
      33 ≠ filterPredicate 44 0 (neg diagonalPredicate.encode) ∧
      35 ≠ filterPredicate 44 0 (neg diagonalPredicate.encode) := by
  have hc := filter_name_gt
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  repeat' apply And.intro
  all_goals omega

/-- Name 34 avoids the entire exact filter graph, including its computed
witness name and all names of the diagonal predicate. -/
theorem filter_graph_fresh : 34 ∉ (namedFilterGraph 44 0 diagonalPredicate).names := by
  have hf : 34 ∉ diagonalPredicate.names := by decide
  have hc : 34 ≠ filterPredicate 44 0 (neg diagonalPredicate.encode) := by
    have h := filter_name_gt
    omega
  simp [namedFilterGraph, namedCounterexampleGraphBody, namedBoth, Formula.names,
    Formula.not, hf, hc]

/-- Any formula whose names are below 45 avoids the computed filter name. -/
theorem filter_fresh_of_bounded (f : Formula) (h : f.names ⊆ Finset.range 45) :
    filterPredicate 44 0 (neg diagonalPredicate.encode) ∉ f.names := by
  intro hf
  have hn := Finset.mem_range.mp (h hf)
  have hc := filter_name_gt
  omega

theorem filter_predicate_fresh :
    filterPredicate 44 0 (neg diagonalPredicate.encode) ∉ diagonalPredicate.names :=
  filter_fresh_of_bounded _ predicate_names_bounded

theorem filter_base_fresh :
    filterPredicate 44 0 (neg diagonalPredicate.encode) ∉
      (namedAllBase 0 34 12 diagonalPredicate).names :=
  filter_fresh_of_bounded _ base_names_bounded

theorem filter_steps_fresh :
    filterPredicate 44 0 (neg diagonalPredicate.encode) ∉
      (namedAllSteps 44 0 33 34 36 37 38 diagonalPredicate).names :=
  filter_fresh_of_bounded _ steps_names_bounded

theorem filter_classification_fresh :
    filterPredicate 44 0 (neg diagonalPredicate.encode) ∉
      (namedAllClassification 44 33 34 12 36 37 38).names :=
  filter_fresh_of_bounded _ classification_names_bounded

/-- The globally quantified container name avoids the exact base schema and
the diagonal predicate specialized at the chosen input name. -/
theorem container_fresh_base : 44 ∉ (namedAllBase 0 34 12 diagonalPredicate).names := by decide

theorem container_fresh_instance :
    44 ∉ (CompactNamed.replace 0 30 diagonalPredicate).names := by decide

end PASoundness.PAtoCompactDiagonalNameBounds

#print axioms PASoundness.PAtoCompactDiagonalNameBounds.predicate_names_bounded
#print axioms PASoundness.PAtoCompactDiagonalNameBounds.steps_names_bounded
#print axioms PASoundness.PAtoCompactDiagonalNameBounds.filter_graph_fresh
#print axioms PASoundness.PAtoCompactDiagonalNameBounds.filter_steps_fresh
