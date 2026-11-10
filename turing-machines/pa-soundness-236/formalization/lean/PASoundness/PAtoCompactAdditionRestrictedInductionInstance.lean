import PASoundness.PAtoCompactCandidateRestrictedInduction
import PASoundness.PAtoCompactAdditionCandidateInductionInstance
import PASoundness.PAtoCompactTermTranslation
import PASoundness.PAtoCompactPartialCompositionFixtureNames

/-! One candidate-container-restricted K induction instance for the literal proposed
addition graph. The zero base and candidate-container-restricted successor step are retained as
explicit K antecedents. This is neither addition totality nor PA induction. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionRestrictedInductionInstance
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactCandidateRestrictedInduction
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactAdditionCandidateInductionInstance (predicate)
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactUniformBase
open PASoundness.PAtoCompactQuantifiedRefutation PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactPartialCompositionFixtureNames
open PASoundness.PAtoCompactCounterexampleSet PASoundness.PAtoCompactUniformStep
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveSuccessor
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def filterName : Nat := filterPredicate 201 31 (neg predicate.encode)

private theorem filter_large : 225 < filterName := by
  have h := member_lt_filter 201 31 (neg predicate.encode)
  have hm : 225 < member 201 31 := by
    have hh := Cantor.left_le_pair 201 31
    unfold member
    omega
  exact Nat.lt_trans hm h

private theorem predicate_names : predicate.names =
    {2,3,4,5,6,19,20,21,22,30,31,32,33,34,35,132,133,134,135,136,137,138,139} := by decide
private theorem predicate_binders : predicate.binders =
    {2,3,4,5,6,19,20,21,22,32,33,34,35,132,133,134,135,136,137,138,139} := by decide
private theorem instance_names : (replace 31 200 predicate).names =
    {2,3,4,5,6,19,20,21,22,30,32,33,34,35,132,133,134,135,136,137,138,139,200} := by decide
private theorem prev_names : (replace 31 204 predicate).names =
    {2,3,4,5,6,19,20,21,22,30,32,33,34,35,132,133,134,135,136,137,138,139,204} := by decide
private theorem succ_names : (replace 31 205 predicate).names =
    {2,3,4,5,6,19,20,21,22,30,32,33,34,35,132,133,134,135,136,137,138,139,205} := by decide

/-- Candidate-domain induction, with base and candidate-restricted successor schemas still inputs. -/
def fixed_induction : KDerivation
    (imp (candidateCode 200 213 209 210 202 31 203 205 206)
      (imp (uniformBaseCode 31 205 207 predicate)
        (imp (allCode 201 (imp (candidateCode 201 213 209 210 202 31 203 205 206)
          (allStepsCode 201 31 204 205 208 209 210 predicate)))
          (replace 31 200 predicate).encode))) := by
  have hWc : 216 ≠ adjunctionPredicate 200 225 := by
    have h := (PAtoCompactAdjunction.predicate_names_lt 200 225).2
    omega
  have hYc : 201 ≠ adjunctionPredicate 200 225 := by
    have h := (PAtoCompactAdjunction.predicate_names_lt 200 225).2
    omega
  have hi := candidate_restricted_induction
    200 201 31 202 203 204 205 206 207 208 209 210 211 212 213 214 215 216
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

/-- The instantiated conclusion keeps the first candidate guard and gives an
output for the literal addition graph at the chosen induction argument. -/
theorem instance_syntax : replace 31 200 predicate =
    .imp (domainAt 100 30) (.ex 32
      (andF (domainAt 100 32) (replace 31 200 additionFormula))) := by decide

theorem fixed_induction_certificate : theoremCode (certificate fixed_induction) =
    imp (candidateCode 200 213 209 210 202 31 203 205 206)
      (imp (uniformBaseCode 31 205 207 predicate)
        (imp (allCode 201 (imp (candidateCode 201 213 209 210 202 31 203 205 206)
          (allStepsCode 201 31 204 205 208 209 210 predicate)))
          (replace 31 200 predicate).encode)) := certificate_correct fixed_induction

end PASoundness.PAtoCompactAdditionRestrictedInductionInstance
#print axioms PASoundness.PAtoCompactAdditionRestrictedInductionInstance.fixed_induction
#print axioms PASoundness.PAtoCompactAdditionRestrictedInductionInstance.instance_syntax
#print axioms PASoundness.PAtoCompactAdditionRestrictedInductionInstance.fixed_induction_certificate
