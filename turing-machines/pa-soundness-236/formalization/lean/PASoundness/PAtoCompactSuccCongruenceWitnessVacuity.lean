import PASoundness.PAtoCompactSuccCongruenceData
import PASoundness.PAtoCompactSuccCongruenceMixedOrder
import PASoundness.PAtoCompactAdjunction

/-! Capture-safe vacuity for the retained successor-congruence premises and
for an existential matrix with a fresh graph binder. All declarations are
literal finite K proofs. This does not construct witnesses or a quotient. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccCongruenceWitnessVacuity
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactGraphRestriction
open PASoundness.PAtoCompactSuccCongruenceData PASoundness.PAtoCompactSuccCongruenceMixedOrder

/-- Named transitivity formula with the exact test labels used in the order
proof. -/
def transitiveNamed (x : Nat) : Formula :=
  .all 37 (.all 38 (.imp (.member x 37) (.imp (.member 37 38) (.member x 38))))

/-- The retained assumptions after deleting the pair and new-graph witness
premises; all graph and transitivity hypotheses remain explicit. -/
def retainedCode : Nat := both oldMatrix (both cleanGraph
  (both sourceSuccessor (both targetSuccessor (both sourceTrans targetTrans))))

def retainedNamed : Formula :=
  namedBoth (namedBoth bijectionFormula orderFormula)
    (namedBoth (.all 19 (.imp (.member 6 19) (edgePredicate 19 0 1)))
      (namedBoth (namedSuccessor 0 7 14)
        (namedBoth (namedSuccessor 1 8 15)
          (namedBoth (transitiveNamed 0) (transitiveNamed 1)))))

theorem retained_encode : retainedNamed.encode = retainedCode := by rfl

/-- The pair-witness name is absent from the retained named formula. -/
def retained_vacuity_11 : KDerivation (imp retainedCode (allCode 11 retainedCode)) := by
  have h := retainedNamed.vacuity 11 (by decide)
  simpa only [retained_encode] using h

/-- The new-graph name is absent from the retained named formula. -/
def retained_vacuity_9 : KDerivation (imp retainedCode (allCode 9 retainedCode)) := by
  have h := retainedNamed.vacuity 9 (by decide)
  simpa only [retained_encode] using h

/-- Exact named matrix and an alpha-renamed existential using fresh binder 33.
This avoids relying on free-name information when generalizing at bound 9. -/
def newMatrixNamed : Formula := namedBoth newBijection newOrder

theorem newMatrix_encode : newMatrixNamed.encode = newMatrix := by rfl

def freshOutput : Formula := .ex 33 (replace 9 33 newMatrixNamed)

def output_vacuity_9 : KDerivation (imp freshOutput.encode (allCode 9 freshOutput.encode)) :=
  freshOutput.vacuity 9 (by decide)

def output_vacuity_11 : KDerivation (imp freshOutput.encode (allCode 11 freshOutput.encode)) :=
  freshOutput.vacuity 11 (by decide)

/-- Exact alpha transport between graph binders 9 and 33. -/
def output_alpha_forward : KDerivation (imp (existsCode 9 newMatrix) freshOutput.encode) := by
  have h := (CompactNamed.existentialAlpha 9 33 newMatrixNamed (by decide) (by decide) (by decide)).1
  simpa only [newMatrix_encode, freshOutput, Formula.encode] using h

def output_alpha_backward : KDerivation (imp freshOutput.encode (existsCode 9 newMatrix)) := by
  have h := (CompactNamed.existentialAlpha 9 33 newMatrixNamed (by decide) (by decide) (by decide)).2
  simpa only [newMatrix_encode, freshOutput, Formula.encode] using h

theorem vacuity_and_alpha_certificates :
    theoremCode (certificate retained_vacuity_11) = imp retainedCode (allCode 11 retainedCode) ∧
    theoremCode (certificate retained_vacuity_9) = imp retainedCode (allCode 9 retainedCode) ∧
    theoremCode (certificate output_vacuity_9) = imp freshOutput.encode (allCode 9 freshOutput.encode) ∧
    theoremCode (certificate output_vacuity_11) = imp freshOutput.encode (allCode 11 freshOutput.encode) ∧
    theoremCode (certificate output_alpha_backward) = imp freshOutput.encode (existsCode 9 newMatrix) :=
  ⟨certificate_correct retained_vacuity_11, certificate_correct retained_vacuity_9,
    certificate_correct output_vacuity_9, certificate_correct output_vacuity_11,
    certificate_correct output_alpha_backward⟩

end PASoundness.PAtoCompactSuccCongruenceWitnessVacuity

#print axioms PASoundness.PAtoCompactSuccCongruenceWitnessVacuity.retained_vacuity_11
#print axioms PASoundness.PAtoCompactSuccCongruenceWitnessVacuity.retained_vacuity_9
#print axioms PASoundness.PAtoCompactSuccCongruenceWitnessVacuity.output_vacuity_9
#print axioms PASoundness.PAtoCompactSuccCongruenceWitnessVacuity.output_vacuity_11
#print axioms PASoundness.PAtoCompactSuccCongruenceWitnessVacuity.output_alpha_backward
#print axioms PASoundness.PAtoCompactSuccCongruenceWitnessVacuity.vacuity_and_alpha_certificates
