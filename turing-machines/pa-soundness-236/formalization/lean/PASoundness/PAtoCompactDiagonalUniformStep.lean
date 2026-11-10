import PASoundness.PAtoCompactDiagonalExistentialStep
import PASoundness.PAtoCompactQuantifiedRefutation
import PASoundness.PAtoCompactDiagonalLocalStep

/-! A uniform candidate-domain induction step for the diagonal invariant.
This constructs actual K proof data but does not establish identity-graph
totality or general collection. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDiagonalUniformStep
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactUniformStep
open PASoundness.PAtoCompactQuantifiedRefutation PASoundness.PAtoCompactDiagonalExistentialStep

def diagonalPredicate : Formula := .ex 11 (invariantNamed 0 11)
def diagonalAt (x : Nat) : Formula := .ex 11 (invariantNamed x 11)

def localStepFormula : Formula :=
  .imp (namedSuccessor 0 1 2) (.imp (diagonalAt 0) (diagonalAt 1))

theorem replace_input : CompactNamed.replace 0 33 localStepFormula =
    .imp (namedSuccessor 33 1 2) (.imp (diagonalAt 33) (diagonalAt 1)) := by decide

theorem replace_output : CompactNamed.replace 1 34
    (.imp (namedSuccessor 33 1 2) (.imp (diagonalAt 33) (diagonalAt 1))) =
    .imp (namedSuccessor 33 34 2) (.imp (diagonalAt 33) (diagonalAt 34)) := by decide

/-- Capture-safe renaming of the local step's two free endpoint labels. -/
def endpoint_specialization
    (hlocal : KDerivation (imp (successorCode 0 1 2)
      (imp (diagonalAt 0).encode (diagonalAt 1).encode))) : KDerivation
    (imp (successorCode 33 34 2) (imp (diagonalAt 33).encode (diagonalAt 34).encode)) := by
  have hi := CompactNamed.universalInstance 0 33 localStepFormula (by decide) (by decide) (by decide)
  rw [replace_input] at hi
  have hgen : KDerivation (allCode 0 localStepFormula.encode) := by
    apply KDerivation.generalize 0
    simpa [localStepFormula, namedSuccessor, namedSuccessorBody, namedBoth, namedEither,
      successorCode, Formula.encode, CompactProof.both, CompactProof.neg, CompactDerivations.either] using hlocal
  have h1 := KDerivation.mp hgen hi
  let f : Formula := .imp (namedSuccessor 33 1 2) (.imp (diagonalAt 33) (diagonalAt 1))
  have hj := CompactNamed.universalInstance 1 34 f (by decide) (by decide) (by decide)
  have hrepl : CompactNamed.replace 1 34 f =
      .imp (namedSuccessor 33 34 2) (.imp (diagonalAt 33) (diagonalAt 34)) := replace_output
  rw [hrepl] at hj
  have h2 := KDerivation.mp (.generalize 1 h1) hj
  simpa [f, namedSuccessor, namedSuccessorBody, namedBoth, namedEither, successorCode,
    Formula.encode, CompactProof.both, CompactProof.neg, CompactDerivations.either] using h2

/-- Capture-safe conversion from successor test name 36 to 2. -/
def successor_test_rename : KDerivation
    (imp (successorCode 33 34 36) (successorCode 33 34 2)) := by
  let f := namedSuccessorBody 33 34 2
  have h := (CompactNamed.universalAlpha 2 36 f (by decide) (by decide) (by decide)).2
  have hrep : CompactNamed.replace 2 36 f = namedSuccessorBody 33 34 36 := by decide
  rw [hrep] at h
  simpa [f, namedSuccessorBody, namedBoth, namedEither, successorCode, Formula.encode,
    CompactProof.both, CompactProof.neg, CompactDerivations.either] using h

/-- The stronger unguarded local step supplies the exact predecessor-core
instance used by the candidate induction interface. -/
def guarded_step
    (hlocal : KDerivation (imp (successorCode 0 1 2)
      (imp (diagonalAt 0).encode (diagonalAt 1).encode))) : KDerivation
    (imp (predecessorCore 44 33 34 36 37 38)
      (imp (diagonalAt 33).encode (diagonalAt 34).encode)) := by
  let C := predecessorCore 44 33 34 36 37 38
  let F := (diagonalAt 33).encode
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [F,C]
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have hf : Context Γ F := .hypothesis (by simp [Γ])
  have hs36 : Context Γ (successorCode 33 34 36) :=
    Context.conjunctionLeft (Context.conjunctionRight hc)
  have hs2 : Context Γ (successorCode 33 34 2) := .mp hs36 (.closed successor_test_rename)
  exact .mp hf (.mp hs2 (.closed (endpoint_specialization hlocal)))

/-- The supplied local K step yields the literal global uniform-step schema. -/
def uniform_step_of_local
    (hlocal : KDerivation (imp (successorCode 0 1 2)
      (imp (diagonalAt 0).encode (diagonalAt 1).encode))) : KDerivation
    (allCode 44 (allStepsCode 44 0 33 34 36 37 38 diagonalPredicate)) := by
  have h := KDerivation.generalize 44 (.generalize 34 (.generalize 33 (guarded_step hlocal)))
  have h33 : CompactNamed.replace 0 33 diagonalPredicate = diagonalAt 33 := by decide
  have h34 : CompactNamed.replace 0 34 diagonalPredicate = diagonalAt 34 := by decide
  change KDerivation (allCode 44 (allCode 34 (allCode 33
    (imp (predecessorCore 44 33 34 36 37 38)
      (imp (CompactNamed.replace 0 33 diagonalPredicate).encode
        (CompactNamed.replace 0 34 diagonalPredicate).encode)))))
  rw [h33, h34]
  exact h

theorem uniform_step_of_local_certificate
    (hlocal : KDerivation (imp (successorCode 0 1 2)
      (imp (diagonalAt 0).encode (diagonalAt 1).encode))) :
    theoremCode (certificate (uniform_step_of_local hlocal)) =
      allCode 44 (allStepsCode 44 0 33 34 36 37 38 diagonalPredicate) :=
  certificate_correct (uniform_step_of_local hlocal)

/-- The literal global uniform-step schema, with the local proof supplied. -/
def uniform_step : KDerivation
    (allCode 44 (allStepsCode 44 0 33 34 36 37 38 diagonalPredicate)) := by
  apply uniform_step_of_local
  exact PAtoCompactDiagonalLocalStep.local_successor_step

theorem uniform_step_certificate : theoremCode (certificate uniform_step) =
    allCode 44 (allStepsCode 44 0 33 34 36 37 38 diagonalPredicate) :=
  certificate_correct uniform_step

end PASoundness.PAtoCompactDiagonalUniformStep

#print axioms PASoundness.PAtoCompactDiagonalUniformStep.uniform_step_of_local
#print axioms PASoundness.PAtoCompactDiagonalUniformStep.uniform_step_of_local_certificate
#print axioms PASoundness.PAtoCompactDiagonalUniformStep.uniform_step
#print axioms PASoundness.PAtoCompactDiagonalUniformStep.uniform_step_certificate
