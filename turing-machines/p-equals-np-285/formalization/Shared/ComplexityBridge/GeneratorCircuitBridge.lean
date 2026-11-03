import Shared.ComplexityBridge.TM2ConstrainedCNF
import Shared.ComplexityBridge.TM2BoundedUnary
import Shared.ComplexityBridge.GeneratorSafeBridge

/-! Reduce the remaining formula-worker obligation to the circuit-data
producer. That producer must be polynomial on all inputs, including inputs
whose binary witness length exceeds the unary budget. -/
namespace Shared.ComplexityBridge.GeneratorCircuitBridge
open Shared.ComplexityBridge
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge.CNF
open Shared.ComplexityBridge.CircuitCNF

abbrev Input := GeneratorSafeBridge.Input
abbrev CircuitData := List Bool × (Nat × List Gate)

def intended (program : Program) (z : Input) : CircuitData :=
  (CircuitWitness.template program (CircuitPairWitness.pairPrefix z.1.1.1) (3*z.2) z.1.1.2.length,
    (CircuitWitness.witnessOutput program (CircuitPairWitness.pairPrefix z.1.1.1) (3*z.2) z.1.1.2.length,
      CircuitWitness.witnessGates program (CircuitPairWitness.pairPrefix z.1.1.1) (3*z.2) z.1.1.2.length))

/-- Exact remaining circuit-generation obligation. Each worker runs in
polynomial time on all encoded requests and supplies the real template, output
wire and gates whenever the binary length lies below the unary budget. -/
def CircuitDataPolyTime : Prop :=
  ∀ program : Program, ∃ F : Input → CircuitData, ComplexityTheory.IsPolyTime F ∧
    ∀ z, TM2BoundedWitnessGuard.generatorGuard z = true → F z = intended program z

/-- The separately proved unary expansion and CNF assembler turn a bounded
circuit-data worker into the exact bounded formula worker. -/
theorem safeFormula_of_circuitData (h : CircuitDataPolyTime) : GeneratorSafeBridge.SafeFormulaPolyTime := by
  intro program
  obtain ⟨F,hF,hcorrect⟩ := h program
  let context : Input → (List Bool × List Bool) × List Bool := fun z => z.1
  let budget : Input → List Bool := fun z => z.1.2
  let n : Input → Nat := fun z => z.2
  let boundArg : Input → List Bool × Nat := fun z => (budget z,n z)
  let tokens : Input → List Bool := fun z => TM2BoundedUnary.expand (boundArg z)
  let fixed : Input → List Bool := fun z => (F z).1
  let other : Input → Nat × List Gate := fun z => (F z).2
  let req : Input → TM2ConstrainedCNF.Input := fun z => ((fixed z,tokens z),other z)
  let result : Input → Formula := fun z => TM2ConstrainedCNF.build (req z)
  have hc : ComplexityTheory.IsPolyTime context := TM2PairFirst.first_isPolyTime
  have hb : ComplexityTheory.IsPolyTime budget := TM2Compose.isPolyTime_comp context
    (fun x : (List Bool × List Bool) × List Bool => x.2) hc TM2GuardAllStep.second_isPolyTime
  have hn : ComplexityTheory.IsPolyTime n := TM2GuardAllStep.second_isPolyTime
  have ha : ComplexityTheory.IsPolyTime boundArg := TM2GuardAllStep.pair_isPolyTime budget n hb hn
  have ht : ComplexityTheory.IsPolyTime tokens := TM2Compose.isPolyTime_comp boundArg TM2BoundedUnary.expand ha TM2BoundedUnary.expand_isPolyTime
  have hf : ComplexityTheory.IsPolyTime fixed := TM2Compose.isPolyTime_comp F
    (fun d : CircuitData => d.1) hF TM2PairFirst.first_isPolyTime
  have ho : ComplexityTheory.IsPolyTime other := TM2Compose.isPolyTime_comp F
    (fun d : CircuitData => d.2) hF TM2GuardAllStep.second_isPolyTime
  have hr : ComplexityTheory.IsPolyTime req := TM2GuardAllStep.pair_isPolyTime
    (fun z => (fixed z,tokens z)) other (TM2GuardAllStep.pair_isPolyTime fixed tokens hf ht) ho
  have hresult : ComplexityTheory.IsPolyTime result := TM2Compose.isPolyTime_comp req TM2ConstrainedCNF.build hr TM2ConstrainedCNF.build_isPolyTime
  refine ⟨result,hresult,?_⟩
  intro z hz
  have hbnd := (TM2BoundedWitnessGuard.generatorGuard_correct z).1 hz
  have hw := hcorrect z hz
  have htok : tokens z = List.replicate z.2 true := TM2BoundedUnary.expand_guarded z.1.2 z.2 hbnd
  change TM2ConstrainedCNF.build (((F z).1,tokens z),(F z).2) = _
  rw [hw,htok]
  simp [intended,TM2ConstrainedCNF.build,CircuitPairWitness.pairFormula]

theorem boundedFormula_of_circuitData (h : CircuitDataPolyTime) : GeneratorUnaryFormula.BoundedPairFormulaPolyTime :=
  GeneratorSafeBridge.boundedFormula_of_safe (safeFormula_of_circuitData h)

theorem pnp_exists_of_circuitData (h : CircuitDataPolyTime) :
    ∃ c : Turing.ToPartrec.Code, (Shared.Beeping.ControllerBinary.machine c).system.EventuallySilent ↔
      ComplexityTheory.P = ComplexityTheory.NP :=
  GeneratorUnaryFormula.pnp_exists_of_boundedFormula (boundedFormula_of_circuitData h)

theorem npconp_exists_of_circuitData (h : CircuitDataPolyTime) :
    ∃ c : Turing.ToPartrec.Code, (Shared.Beeping.ControllerBinary.machine c).system.EventuallySilent ↔
      ComplexityTheory.NP = ComplexityTheory.coNP :=
  GeneratorUnaryFormula.npconp_exists_of_boundedFormula (boundedFormula_of_circuitData h)
end Shared.ComplexityBridge.GeneratorCircuitBridge
