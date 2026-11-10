import PASoundness.PAtoCompactCandidateGlobalInduction
import PASoundness.PAtoCompactDiagonalUniformBase
import PASoundness.PAtoCompactDiagonalUniformStep
import PASoundness.PAtoCompactDiagonalNameBounds

/-! Concrete instantiation of conditional candidate-domain K induction at the
represented diagonal-graph predicate. The candidate-domain condition remains
an explicit premise; no unrestricted identity-graph totality or PA proof
translation is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDiagonalCandidateInduction
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactCandidateGlobalInduction PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactQuantifiedRefutation PASoundness.PAtoCompactUniformBase
open PASoundness.PAtoCompactDiagonalUniformBase
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A provisional composition retaining only the displayed complex named
freshness side conditions. The base and global step are actual K derivations. -/
def diagonal_from_candidate_of_fresh
    (hcOthers : filterPredicate 44 0 (neg diagonalPredicate.encode) ∉ [30,32,34,35])
    (hcf : filterPredicate 44 0 (neg diagonalPredicate.encode) ∉ diagonalPredicate.names)
    (hmGraph : 34 ∉ (namedFilterGraph 44 0 diagonalPredicate).names)
    (hcBase : filterPredicate 44 0 (neg diagonalPredicate.encode) ∉ (namedAllBase 0 34 12 diagonalPredicate).names)
    (hcStep : filterPredicate 44 0 (neg diagonalPredicate.encode) ∉ (namedAllSteps 44 0 33 34 36 37 38 diagonalPredicate).names)
    (hcClass : filterPredicate 44 0 (neg diagonalPredicate.encode) ∉ (namedAllClassification 44 33 34 12 36 37 38).names) :
    KDerivation (imp (candidateCode 30 41 37 38 32 0 31 34 35)
      (CompactNamed.replace 0 30 diagonalPredicate).encode) := by
  have hbig := (filterPredicate_bounds 44 0 (neg diagonalPredicate.encode)).1
  have hWc : 45 ≠ adjunctionPredicate 30 54 := by
    have h := (PAtoCompactAdjunction.predicate_names_lt 30 54).2
    omega
  have hYc : 44 ≠ adjunctionPredicate 30 54 := by
    have h := (PAtoCompactAdjunction.predicate_names_lt 30 54).2
    omega
  have hvc : 33 ≠ filterPredicate 44 0 (neg diagonalPredicate.encode) := by omega
  have hrc : 35 ≠ filterPredicate 44 0 (neg diagonalPredicate.encode) := by omega
  have hYBase : 44 ∉ (namedAllBase 0 34 12 diagonalPredicate).names := by decide
  have hYInst : 44 ∉ (CompactNamed.replace 0 30 diagonalPredicate).names := by decide
  have hi : KDerivation
      (imp (candidateCode 30 41 37 38 32 0 31 34 35)
        (imp (uniformBaseCode 0 34 12 diagonalPredicate)
          (imp (allCode 44 (allStepsCode 44 0 33 34 36 37 38 diagonalPredicate))
            (CompactNamed.replace 0 30 diagonalPredicate).encode))) := by
    apply candidate_global_induction 30 44 0 32 31 33 34 35 12 36 37 38 39 40 41 42 43 45 46 47 48 49 50 51 52 53 54 diagonalPredicate
    all_goals first | assumption | decide
  apply Context.closeEmpty
  apply Context.deduction
  have hd : Context [candidateCode 30 41 37 38 32 0 31 34 35]
      (candidateCode 30 41 37 38 32 0 31 34 35) := Context.head [] _
  have hs : KDerivation (allCode 44 (allStepsCode 44 0 33 34 36 37 38 diagonalPredicate)) :=
    PAtoCompactDiagonalUniformStep.uniform_step
  exact .mp (.closed hs) (.mp (.closed uniform_diagonal_base) (.mp hd (.closed hi)))

/-- Every object satisfying the displayed candidate predicate has a
represented diagonal graph with coverage and no-garbage. This is an explicit
K derivation for the displayed fresh labels, conditional on the candidate
formula, and does not assert unrestricted graph collection. -/
def candidate_diagonal_graph_exists : KDerivation
    (imp (candidateCode 30 41 37 38 32 0 31 34 35)
      (existsCode 11 (PAtoCompactDiagonalExistentialStep.invariantNamed 30 11).encode)) := by
  have h := diagonal_from_candidate_of_fresh
    PAtoCompactDiagonalNameBounds.filter_avoids_auxiliaries.1
    PAtoCompactDiagonalNameBounds.filter_predicate_fresh
    PAtoCompactDiagonalNameBounds.filter_graph_fresh
    PAtoCompactDiagonalNameBounds.filter_base_fresh
    PAtoCompactDiagonalNameBounds.filter_steps_fresh
    PAtoCompactDiagonalNameBounds.filter_classification_fresh
  have hr : CompactNamed.replace 0 30 diagonalPredicate =
      .ex 11 (PAtoCompactDiagonalExistentialStep.invariantNamed 30 11) := by decide
  rw [hr] at h
  exact h

theorem candidate_diagonal_graph_exists_certificate :
    theoremCode (certificate candidate_diagonal_graph_exists) =
      imp (candidateCode 30 41 37 38 32 0 31 34 35)
        (existsCode 11 (PAtoCompactDiagonalExistentialStep.invariantNamed 30 11).encode) :=
  certificate_correct candidate_diagonal_graph_exists

end PASoundness.PAtoCompactDiagonalCandidateInduction

#print axioms PASoundness.PAtoCompactDiagonalCandidateInduction.candidate_diagonal_graph_exists
#print axioms PASoundness.PAtoCompactDiagonalCandidateInduction.candidate_diagonal_graph_exists_certificate
