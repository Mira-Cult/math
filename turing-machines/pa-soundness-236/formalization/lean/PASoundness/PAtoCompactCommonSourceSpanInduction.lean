import PASoundness.PAtoCompactCommonSourceSpanGlobalStep
import PASoundness.PAtoCompactCandidateGlobalInduction
import PASoundness.PAtoCompactPartialCompositionAtSource
import PASoundness.PAtoCompactScopedActiveReplace

/-! Candidate induction for collecting the common-source span of two supplied
forward-bijection graphs. The base, successor, candidate guard and exact input
clauses are literal finite K proof data. This is a draft source construction;
it neither assumes the two image objects are candidates nor by itself proves
sum gluing, quotient congruence or the PA/machine equivalence. -/
namespace PASoundness.PAtoCompactCommonSourceSpanInduction

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactCandidateGlobalInduction
open PASoundness.PAtoCompactUniformBase PASoundness.PAtoCompactQuantifiedRefutation
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactCommonSourceSpanBase PASoundness.PAtoCompactCommonSourceSpanImages
open PASoundness.PAtoCompactCommonSourceSpanSuccessor PASoundness.PAtoCompactCommonSourceSpanFixtureNames
open PASoundness.PAtoCompactCommonSourceSpanGlobalStep PASoundness.PAtoCompactPartialCompositionAtSource

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Concrete candidate induction with all name-allocation hypotheses checked. -/
def fixed_induction : KDerivation
    (imp (candidateCode 25 37 32 33 34 30 35 13 36)
      (imp (uniformBaseCode 30 13 11 predicate)
        (imp (allCode 31 (allStepsCode 31 30 10 13 15 32 33 predicate))
          (replace 30 25 predicate).encode))) := by
  have h := candidate_global_induction
    25 31 30 34 35 10 13 36 11 15 32 33 38 39 37 40 41 42
    43 44 45 46 47 48 49 51 50 predicate
    chosen_successor_fresh selector_guards.1 selector_guards.2
    fresh_nonempty fresh_induction fresh_domain fresh_outer fresh_alpha
    (by decide) (by decide) induction_name_unbound instance_name_unbound
    filter_avoids_aux.1 filter_avoids_predicate
    (by decide) (by decide) (by decide) (by decide)
    predicate_aux_fresh.1 predicate_aux_fresh.2
    (by decide) (by decide) (by decide)
    filter_avoids_aux.2.1 filter_avoids_aux.2.2
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    graph_aux_fresh filter_base_fresh filter_step_fresh filter_class_fresh
    container_base_fresh container_instance_fresh
  exact h

/-- The actual empty-prefix construction is the induction base instance. -/
def empty_instance : KDerivation
    (imp (zeroCode 10 11) (replace 30 10 predicate).encode) := by
  simpa only [predicate, old_instance, oldExists, Formula.encode] using empty_prefix_span_exists

/-- Universal zero base, with prefix variable 13. -/
def exact_uniform_base : KDerivation (uniformBaseCode 30 13 11 predicate) := by
  let body := namedUniformBaseBody 30 10 11 predicate
  have hone : KDerivation (allCode 10 body.encode) := .generalize 10 empty_instance
  have halpha := (universalAlpha 10 13 body (by decide) (by decide) (by decide)).1
  have he : replace 10 13 body = namedUniformBaseBody 30 13 11 predicate := by decide
  rw [he] at halpha
  exact .mp hone halpha

def candidatePrefix : Nat := candidateCode 25 37 32 33 34 30 35 13 36

theorem candidate_instance : replace 30 25 predicate =
    .ex 9 (replace 10 25 spanComposition) := by decide

/-- K constructs a span graph over every candidate prefix at 25. The two
forward clauses remain explicit; the image objects are not candidate-guarded. -/
def candidate_prefix_span : KDerivation (imp firstClause.encode (imp secondClause.encode
    (imp candidatePrefix (existsCode 9 (replace 10 25 spanComposition).encode)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [candidatePrefix,secondClause.encode,firstClause.encode]
  have hd : Context Γ candidatePrefix := .head _ _
  have hs : Context Γ secondClause.encode := .hypothesis (by simp [Γ])
  have hf : Context Γ firstClause.encode := .hypothesis (by simp [Γ])
  have hbase : Context Γ (uniformBaseCode 30 13 11 predicate) := .closed exact_uniform_base
  have hstep : Context Γ (allCode 31 (allStepsCode 31 30 10 13 15 32 33 predicate)) := by
    simpa only [predicate] using Context.mp hs (Context.mp hf (.closed global_step))
  have hi : Context Γ (replace 30 25 predicate).encode :=
    .mp hstep (.mp hbase (.mp hd (.closed fixed_induction)))
  rw [candidate_instance] at hi
  exact hi

private def frame (x : Nat) : Formula := .imp firstClause (.imp secondClause
  (.imp (namedCandidate x) (.ex 9 (replace 10 x spanComposition))))

private theorem frame25_code : (frame 25).encode =
    imp firstClause.encode (imp secondClause.encode
      (imp candidatePrefix (existsCode 9 (replace 10 25 spanComposition).encode))) := by
  rfl

/-- Specialize the candidate prefix to the common source itself, allowing the
common source and prefix names to denote the same object. -/
def common_source_span : KDerivation
    (imp firstClause.encode (imp secondClause.encode
      (imp (namedCandidate 1).encode (existsCode 9 (replace 10 1 spanComposition).encode)))) := by
  have hframe : KDerivation (frame 25).encode := by
    rw [frame25_code]
    exact candidate_prefix_span
  have h := replace_derivation 25 1 (frame 25) (by decide) (by decide) hframe
  have hreplace : replace 25 1 (frame 25) = frame 1 := by decide
  rw [hreplace] at h
  simpa only [frame, Formula.encode] using h

theorem common_source_span_certificate : theoremCode (certificate common_source_span) =
    imp firstClause.encode (imp secondClause.encode
      (imp (namedCandidate 1).encode (existsCode 9 (replace 10 1 spanComposition).encode))) :=
  certificate_correct common_source_span

end PASoundness.PAtoCompactCommonSourceSpanInduction

#print axioms PASoundness.PAtoCompactCommonSourceSpanInduction.fixed_induction
#print axioms PASoundness.PAtoCompactCommonSourceSpanInduction.empty_instance
#print axioms PASoundness.PAtoCompactCommonSourceSpanInduction.exact_uniform_base
#print axioms PASoundness.PAtoCompactCommonSourceSpanInduction.candidatePrefix
#print axioms PASoundness.PAtoCompactCommonSourceSpanInduction.candidate_instance
#print axioms PASoundness.PAtoCompactCommonSourceSpanInduction.candidate_prefix_span
#print axioms PASoundness.PAtoCompactCommonSourceSpanInduction.common_source_span
#print axioms PASoundness.PAtoCompactCommonSourceSpanInduction.common_source_span_certificate
