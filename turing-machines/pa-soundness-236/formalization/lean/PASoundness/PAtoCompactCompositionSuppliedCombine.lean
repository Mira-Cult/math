import PASoundness.PAtoCompactCompositionSuppliedVacuity
import PASoundness.PAtoCompactPartialInverseCombine

/-! A finite K constructor combining supplied quantified forward and backward
composition-coverage proofs into the exact renamed successor invariant.
It assumes both clause derivations and constructs no witnesses or graph. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCompositionSuppliedCombine
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactPartialCompositionBase PASoundness.PAtoCompactCompositionSuppliedVacuity
open PASoundness.PAtoCompactPartialInverseCombine
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def path : Formula := .ex 4 (namedBoth (.member 1 4)
  (namedBoth (graphFormula 6 2 4) (graphFormula 7 4 3)))

def forwardCoverage : Formula := .all 2 (.all 3
  (.imp (namedBoth (.member 0 2) (.member 8 3))
    (.imp (namedBoth (.member 13 2) path) (graphFormula 17 2 3))))

def backwardCoverage : Formula := .all 2 (.all 3
  (.imp (namedBoth (.member 0 2) (.member 8 3))
    (.imp (graphFormula 17 2 3) (namedBoth (.member 13 2) path))))

def nextPartial : Formula := replace 10 13 (replace 9 17 partialComposition)

/-- Explicit syntax alignment, with backward direction followed by forward. -/
theorem next_partial_code : nextPartial.encode =
    allCode 2 (allCode 3 (imp (both (member 0 2) (member 8 3))
      (both (imp (graphFormula 17 2 3).encode (both (member 13 2) path.encode))
        (imp (both (member 13 2) path.encode) (graphFormula 17 2 3).encode)))) := by rfl

/-- Both proof-data arguments retain the complete supplied-premises antecedent. -/
def combine
    (forward : KDerivation (imp suppliedPremises.encode forwardCoverage.encode))
    (backward : KDerivation (imp suppliedPremises.encode backwardCoverage.encode)) :
    KDerivation (imp suppliedPremises.encode nextPartial.encode) := by
  let Q := both (member 0 2) (member 8 3)
  let T := both (member 13 2) path.encode
  let G := (graphFormula 17 2 3).encode
  have hc := all2_guard_conjoin 2 3 Q (imp G T) (imp T G)
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [suppliedPremises.encode]
  have hp : Context Γ suppliedPremises.encode := Context.head [] _
  have hf : Context Γ forwardCoverage.encode := .mp hp (.closed forward)
  have hb : Context Γ backwardCoverage.encode := .mp hp (.closed backward)
  have hnew : Context Γ (allCode 2 (allCode 3 (imp Q (both (imp G T) (imp T G))))) :=
    .mp hf (.mp hb (.closed hc))
  exact hnew

theorem combine_certificate
    (forward : KDerivation (imp suppliedPremises.encode forwardCoverage.encode))
    (backward : KDerivation (imp suppliedPremises.encode backwardCoverage.encode)) :
    theoremCode (certificate (combine forward backward)) =
      imp suppliedPremises.encode nextPartial.encode := certificate_correct (combine forward backward)

end PASoundness.PAtoCompactCompositionSuppliedCombine

#print axioms PASoundness.PAtoCompactCompositionSuppliedCombine.combine
#print axioms PASoundness.PAtoCompactCompositionSuppliedCombine.combine_certificate
