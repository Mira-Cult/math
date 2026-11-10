import PASoundness.PAtoCompactProductMatchInductionFixture
import PASoundness.PAtoCompactScopedActiveReplace

/-! Specialize the candidate-prefix partial-match induction at the source
output domain. The global nonempty extension step remains an explicit
object-level antecedent: this is not an unconditional collection proof. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchCollectionConditional

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveDomain
open PASoundness.PAtoCompactPredecessor PASoundness.PAtoCompactLeastCounterexample
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactQuantifiedRefutation
open PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactProductMatchPartialBase PASoundness.PAtoCompactProductMatchInductionFixture

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def candidateFormula (x : Nat) : Formula :=
  namedBoth (namedBoth (namedTransitive x 77 78) (namedMembersTransitive x 81 77 78))
    (namedBoth (.all 72 (namedGreatestSubsetsBody x 72 64 59 75))
      (.all 72 (namedLeastSubsetsBody x 72 64 73 59 75)))

theorem candidate_formula_code (x : Nat) : (candidateFormula x).encode =
    candidateCode x 81 77 78 72 64 73 59 75 := by rfl

def stepFormula : Formula := .all 71 (namedAllSteps 71 64 74 59 76 77 78 predicate)

theorem step_formula_code : stepFormula.encode = globalStep := by
  simp only [stepFormula, globalStep, Formula.encode, named_all_steps_encode]

def sourceFrame : Formula := .imp (candidateFormula 70)
  (.imp stepFormula (.ex 58 (replace 59 70 partialMatch)))

def actualFrame : Formula := .imp (candidateFormula 2)
  (.imp stepFormula (.ex 58 (replace 59 2 partialMatch)))

theorem source_frame_fresh : 70 ∉ sourceFrame.binders ∧ 2 ∉ sourceFrame.binders := by decide

theorem source_substitution : replace 70 2 sourceFrame = actualFrame := by decide

/-- The source output domain is name 2. Under its candidate condition and a
literal proof of the indicated global partial-match extension step, K
constructs a represented matching graph on all guarded endpoints. -/
def source_collection_of_step : KDerivation
    (imp (candidateCode 2 81 77 78 72 64 73 59 75) (imp globalStep
      (existsCode 58 (replace 59 2 partialMatch).encode))) := by
  have h : KDerivation sourceFrame.encode := by
    simpa only [sourceFrame, Formula.encode, candidate_formula_code, step_formula_code,
      candidatePrefix] using prefix_collection_of_step
  have hi := replace_derivation 70 2 sourceFrame source_frame_fresh.1 source_frame_fresh.2 h
  rw [source_substitution] at hi
  simpa only [actualFrame, Formula.encode, candidate_formula_code, step_formula_code] using hi

theorem source_collection_of_step_certificate :
    theoremCode (certificate source_collection_of_step) =
      imp (candidateCode 2 81 77 78 72 64 73 59 75) (imp globalStep
        (existsCode 58 (replace 59 2 partialMatch).encode)) := certificate_correct _

end PASoundness.PAtoCompactProductMatchCollectionConditional

#print axioms PASoundness.PAtoCompactProductMatchCollectionConditional.candidate_formula_code
#print axioms PASoundness.PAtoCompactProductMatchCollectionConditional.step_formula_code
#print axioms PASoundness.PAtoCompactProductMatchCollectionConditional.source_collection_of_step
#print axioms PASoundness.PAtoCompactProductMatchCollectionConditional.source_collection_of_step_certificate
