import Shared.ComplexityBridge.TM2ListMask
import Shared.ComplexityBridge.TM2BoundedWitnessGuard

/-! The guard and output mask are implemented. A remaining formula worker
must run in polynomial time on every input and return the exact formula on
budget-valid inputs; it may return any formula when the guard is false. -/
namespace Shared.ComplexityBridge.GeneratorSafeBridge
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge.CNF
open Shared.ComplexityBridge

abbrev Input := ((List Bool × List Bool) × List Bool) × Nat

def SafeFormulaPolyTime : Prop :=
  ∀ program : Program, ∃ F : Input → Formula, ComplexityTheory.IsPolyTime F ∧
    ∀ z, TM2BoundedWitnessGuard.generatorGuard z = true →
      F z = CircuitPairWitness.pairFormula program z.1.1.1 z.2 z.1.1.2.length

/-- Combining an everywhere polynomial-time safe worker with the proved
guard and finite output mask implements the exact bounded constructor. -/
theorem boundedFormula_of_safe (h : SafeFormulaPolyTime) :
    GeneratorUnaryFormula.BoundedPairFormulaPolyTime := by
  intro program
  obtain ⟨F,hF,hcorrect⟩ := h program
  let prep : Input → Bool × Formula := fun z => (TM2BoundedWitnessGuard.generatorGuard z,F z)
  have hp : ComplexityTheory.IsPolyTime prep := TM2GuardAllStep.pair_isPolyTime _ _
    TM2BoundedWitnessGuard.generatorGuard_isPolyTime hF
  have hc := TM2Compose.isPolyTime_comp prep (TM2ListMask.mask (α := Clause)) hp TM2ListMask.mask_isPolyTime
  have he : (fun z => TM2ListMask.mask (prep z)) = GeneratorUnaryFormula.boundedPairFormula program := by
    funext z
    rw [TM2BoundedWitnessGuard.boundedPairFormula_guard]
    cases hg : TM2BoundedWitnessGuard.generatorGuard z with
    | false => simp [prep,TM2ListMask.mask,hg]
    | true => simp [prep,TM2ListMask.mask,hg,hcorrect z hg]
  rw [←he]
  exact hc

/-- The safe-worker interface is equivalent to the original bounded
constructor obligation; it introduces no stronger claim about invalid inputs. -/
theorem safe_iff_boundedFormula : SafeFormulaPolyTime ↔
    GeneratorUnaryFormula.BoundedPairFormulaPolyTime := by
  constructor
  · exact boundedFormula_of_safe
  · intro h program
    refine ⟨GeneratorUnaryFormula.boundedPairFormula program,h program,?_⟩
    intro z hz
    rw [TM2BoundedWitnessGuard.boundedPairFormula_guard,hz]
    rfl

end Shared.ComplexityBridge.GeneratorSafeBridge
