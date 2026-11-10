import PASoundness.PAtoCompactCandidateRestrictedInduction
import PASoundness.PAtoCompactFixedFirstPreservedBase
import PASoundness.PAtoCompactPartialCompositionFixtureNames

/-! A candidate-container-restricted induction instance for the fixed-first
row graph invariant. Both the uniform zero base and the restricted successor
schema are retained as explicit K antecedents. This does not construct the
row graph, prove multiplication totality, or assert PA proof transport. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactFixedFirstRestrictedInduction
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactCandidateRestrictedInduction
open PASoundness.PAtoCompactFixedFirstPreservedBase
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactUniformBase
open PASoundness.PAtoCompactQuantifiedRefutation PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactPartialCompositionFixtureNames
open PASoundness.PAtoCompactCounterexampleSet PASoundness.PAtoCompactUniformStep
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveSuccessor
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Existence of a preserved, covered and no-garbage fixed-first row graph
for the prefix named 0. Name 31 is the fixed source; it remains free. -/
def predicate : Formula := .ex 7 (rowInvariantPreserved 7)

def filterName : Nat := filterPredicate 201 0 (neg predicate.encode)

private theorem filter_large : 225 < filterName := by
  have h := member_lt_filter 201 0 (neg predicate.encode)
  have hm : 225 < member 201 0 := by
    have hh := Cantor.left_le_pair 201 0
    unfold member
    omega
  exact Nat.lt_trans hm h

private theorem predicate_names : predicate.names =
    {0,3,4,5,6,7,9,10,19,20,21,22,30,31} := by decide
private theorem predicate_binders : predicate.binders =
    {3,4,5,7,9,19,20,21,22} := by decide
private theorem instance_names : (replace 0 31 predicate).names =
    {3,4,5,6,7,9,10,19,20,21,22,30,31} := by decide
private theorem prev_names : (replace 0 204 predicate).names =
    {3,4,5,6,7,9,10,19,20,21,22,30,31,204} := by decide
private theorem succ_names : (replace 0 205 predicate).names =
    {3,4,5,6,7,9,10,19,20,21,22,30,31,205} := by decide

/-- At candidate source 31, the full-source row invariant follows from the
explicit uniform zero base and candidate-container-restricted step. Replacing
the prefix 0 by the existing free source name 31 is intentional aliasing. -/
def fixed_induction : KDerivation
    (imp (candidateCode 31 213 209 210 202 0 203 205 206)
      (imp (uniformBaseCode 0 205 207 predicate)
        (imp (allCode 201 (imp (candidateCode 201 213 209 210 202 0 203 205 206)
          (allStepsCode 201 0 204 205 208 209 210 predicate)))
          (replace 0 31 predicate).encode))) := by
  have hWc : 216 ≠ adjunctionPredicate 31 225 := by
    have h := (PAtoCompactAdjunction.predicate_names_lt 31 225).2
    omega
  have hYc : 201 ≠ adjunctionPredicate 31 225 := by
    have h := (PAtoCompactAdjunction.predicate_names_lt 31 225).2
    omega
  have hi := candidate_restricted_induction
    31 201 0 202 203 204 205 206 207 208 209 210 211 212 213 214 215 216
    217 218 219 220 221 222 223 224 225 predicate
    (by decide) hWc hYc
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [predicate_binders]; decide) (by rw [predicate_binders]; decide) ?_ ?_
    (by decide) (by decide) (by decide) (by decide)
    (by rw [predicate_names]; decide) (by rw [predicate_names]; decide) (by decide) (by decide) (by decide) ?_ ?_
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    ?_ ?_ ?_ ?_ ?_ ?_
  case refine_1 =>
    have hf := filter_large
    simp only [filterName] at hf
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    omega
  case refine_2 =>
    rw [predicate_names]
    have hf := filter_large
    simp only [filterName] at hf
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    omega
  case refine_3 =>
    have hf := filter_large
    simp only [filterName] at hf
    omega
  case refine_4 =>
    have hf := filter_large
    simp only [filterName] at hf
    omega
  case refine_5 =>
    have hf := filter_large
    simp only [filterName] at hf
    simp only [namedFilterGraph, namedCounterexampleGraphBody, namedBoth, Formula.not,
      Formula.names, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, not_false_eq_true, not_or, predicate_names, and_true]
    omega
  case refine_6 =>
    have hf := filter_large
    simp only [filterName] at hf
    simp only [namedAllBase, namedUniformBaseBody, Formula.names, Finset.mem_insert,
      Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty, not_false_eq_true, not_or,
      succ_names, and_true]
    omega
  case refine_7 =>
    have hf := filter_large
    simp only [filterName] at hf
    simp only [namedAllSteps, namedUniformStepBody, namedPredecessorCore, namedBoth,
      namedSuccessorBody, namedEither, transitiveBody, Formula.names, Finset.mem_insert,
      Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty, not_false_eq_true,
      not_or, prev_names, succ_names, and_true]
    omega
  case refine_8 =>
    have hf := filter_large
    simp only [filterName] at hf
    simp only [namedAllClassification, namedPredecessorCore, namedBoth, namedSuccessorBody,
      namedEither, transitiveBody, Formula.names, Finset.mem_insert, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, not_false_eq_true, not_or, and_true]
    omega
  case refine_9 =>
    simp only [namedAllBase, namedUniformBaseBody, Formula.names, Finset.mem_insert,
      Finset.mem_union, Finset.mem_singleton, not_or, succ_names]
    decide
  case refine_10 =>
    rw [instance_names]
    decide
  case refine_11 => exact hi

theorem fixed_induction_certificate : theoremCode (certificate fixed_induction) =
    imp (candidateCode 31 213 209 210 202 0 203 205 206)
      (imp (uniformBaseCode 0 205 207 predicate)
        (imp (allCode 201 (imp (candidateCode 201 213 209 210 202 0 203 205 206)
          (allStepsCode 201 0 204 205 208 209 210 predicate)))
          (replace 0 31 predicate).encode)) := certificate_correct fixed_induction
end PASoundness.PAtoCompactFixedFirstRestrictedInduction
#print axioms PASoundness.PAtoCompactFixedFirstRestrictedInduction.fixed_induction
#print axioms PASoundness.PAtoCompactFixedFirstRestrictedInduction.fixed_induction_certificate
