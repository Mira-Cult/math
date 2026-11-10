import PASoundness.PeanoBetaCRTConcreteSuccessor
import PASoundness.PeanoBetaCRTFuturePair

/-! The fixed-name bounded CRT successor, under explicit residue-totality,
ordered-pair inverse, and k<N formulas. The PA derivation has no supplied
component-update proof premise. No induction or bounded CRT is asserted. -/
namespace PASoundness.PeanoBetaCRTStepClosed
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic
open PeanoBetaCRTInvariant PeanoBetaCRTAlignment

/-- The exact side formula: every required residue exists and is bounded,
the current index is below N, and every ordered pair of beta moduli through
N has an inverse certificate. -/
def side (φ : Peano.Formula) : Peano.Formula :=
  PeanoBetaCRTConcreteSuccessor.assumptions φ PeanoBetaCRTFuturePair.endpointAt8

private theorem endpoint_names_fresh :
    ∀ x ∈ ([9,10,13,14,15] : List Nat), x ∉ PeanoBetaCRTFuturePair.endpointAt8.freeVarFinset := by
  intro x hx
  apply PeanoBetaCRTFuturePair.endpoint_fresh x
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide

/-- PA derives the concrete successor update from the displayed object-level
side condition, with no supplied row/factor/future component derivations. -/
theorem successor (φ : Peano.Formula) (hφ : NamesSafe φ) :
    FormulaProves ((side φ).imp ((currentInvariant φ).imp (nextInvariant φ))) := by
  apply PeanoBetaCRTConcreteSuccessor.successor φ PeanoBetaCRTFuturePair.endpointAt8 hφ endpoint_names_fresh
  simpa only [side, PeanoBetaCRTConcreteSuccessor.assumptions] using
    (PeanoBetaCRTFuturePair.future_component_with_side φ
      (PeanoBetaCRTResidueSelect.assumptions φ) (rowAssumptions φ))

/-- The same conditional update, rewritten to the literal PA successor
substitution. This is a single step; no PA induction has been applied. -/
theorem literal_successor (φ : Peano.Formula) (hφ : NamesSafe φ) :
    FormulaProves ((side φ).imp ((currentInvariant φ).imp
      (FOL.substAt (currentInvariant φ) 7 (succ (.var 7))))) := by
  apply PeanoBetaCRTConcreteSuccessor.literal_successor φ PeanoBetaCRTFuturePair.endpointAt8 hφ endpoint_names_fresh
  simpa only [side, PeanoBetaCRTConcreteSuccessor.assumptions] using
    (PeanoBetaCRTFuturePair.future_component_with_side φ
      (PeanoBetaCRTResidueSelect.assumptions φ) (rowAssumptions φ))

/-- Universal closure retains the k<N side condition inside the quantifier. -/
theorem literal_successor_all (φ : Peano.Formula) (hφ : NamesSafe φ) :
    FormulaProves (FOL.allAt 7 ((side φ).imp ((currentInvariant φ).imp
      (FOL.substAt (currentInvariant φ) 7 (succ (.var 7)))))) :=
  .generalize 7 (literal_successor φ hφ)

end PASoundness.PeanoBetaCRTStepClosed
