import Shared.ComplexityBridge.TM2CircuitTemplate
import Shared.ComplexityBridge.GeneratorCircuitBridge

/-! The actual template portion of the circuit-data worker is discharged.
Only the output-wire and gate-list producer remains conditional. -/
namespace Shared.ComplexityBridge.GeneratorTemplateBridge
open Shared.ComplexityBridge
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge.CNF
open Shared.ComplexityBridge.CircuitCNF
open Shared.ComplexityBridge.GeneratorCircuitBridge

abbrev GateData := Nat × List Gate

def intendedGates (program : Program) (z : Input) : GateData := (intended program z).2

def GateDataPolyTime : Prop :=
  ∀ program : Program, ∃ F : Input → GateData, ComplexityTheory.IsPolyTime F ∧
    ∀ z, TM2BoundedWitnessGuard.generatorGuard z = true → F z = intendedGates program z

def templateWorker (program : Program) (z : Input) : List Bool :=
  TM2CircuitTemplate.build program
    ((CircuitPairWitness.pairPrefix z.1.1.1,TM2BoundedUnary.expand (z.1.2,z.2)),z.1.1.2)

theorem templateWorker_isPolyTime (program : Program) : ComplexityTheory.IsPolyTime (templateWorker program) := by
  let ctx : Input → (List Bool × List Bool) × List Bool := fun z => z.1
  let pair : Input → List Bool × List Bool := fun z => z.1.1
  let publicBits : Input → List Bool := fun z => z.1.1.1
  let fuel : Input → List Bool := fun z => z.1.1.2
  let budget : Input → List Bool := fun z => z.1.2
  let value : Input → Nat := fun z => z.2
  let pubPrefix : Input → List Bool := fun z => CircuitPairWitness.pairPrefix (publicBits z)
  let expandArg : Input → List Bool × Nat := fun z => (budget z,value z)
  let tokens : Input → List Bool := fun z => TM2BoundedUnary.expand (expandArg z)
  let req : Input → TM2CircuitTemplate.Input := fun z => ((pubPrefix z,tokens z),fuel z)
  have hc : ComplexityTheory.IsPolyTime ctx := TM2PairFirst.first_isPolyTime
  have hp : ComplexityTheory.IsPolyTime pair := TM2Compose.isPolyTime_comp ctx
    (fun q : (List Bool × List Bool) × List Bool => q.1) hc TM2PairFirst.first_isPolyTime
  have hpub : ComplexityTheory.IsPolyTime publicBits := TM2Compose.isPolyTime_comp pair
    (fun q : List Bool × List Bool => q.1) hp TM2PairFirst.first_isPolyTime
  have hf : ComplexityTheory.IsPolyTime fuel := TM2Compose.isPolyTime_comp pair
    (fun q : List Bool × List Bool => q.2) hp TM2GuardAllStep.second_isPolyTime
  have hb : ComplexityTheory.IsPolyTime budget := TM2Compose.isPolyTime_comp ctx
    (fun q : (List Bool × List Bool) × List Bool => q.2) hc TM2GuardAllStep.second_isPolyTime
  have hv : ComplexityTheory.IsPolyTime value := TM2GuardAllStep.second_isPolyTime
  have hprefix : ComplexityTheory.IsPolyTime pubPrefix := TM2Compose.isPolyTime_comp publicBits
    CircuitPairWitness.pairPrefix hpub GeneratorFamilyBridge.pairPrefix_isPolyTime
  have hea : ComplexityTheory.IsPolyTime expandArg := TM2GuardAllStep.pair_isPolyTime budget value hb hv
  have ht : ComplexityTheory.IsPolyTime tokens := TM2Compose.isPolyTime_comp expandArg TM2BoundedUnary.expand hea TM2BoundedUnary.expand_isPolyTime
  have hreq : ComplexityTheory.IsPolyTime req := TM2GuardAllStep.pair_isPolyTime
    (fun z => (pubPrefix z,tokens z)) fuel (TM2GuardAllStep.pair_isPolyTime pubPrefix tokens hprefix ht) hf
  have h := TM2Compose.isPolyTime_comp req (TM2CircuitTemplate.build program) hreq (TM2CircuitTemplate.build_isPolyTime program)
  change ComplexityTheory.IsPolyTime (fun z : Input => TM2CircuitTemplate.build program
    ((CircuitPairWitness.pairPrefix z.1.1.1,TM2BoundedUnary.expand (z.1.2,z.2)),z.1.1.2))
  exact h

theorem templateWorker_correct (program : Program) (z : Input)
    (h : TM2BoundedWitnessGuard.generatorGuard z = true) :
    templateWorker program z = (intended program z).1 := by
  have hb := (TM2BoundedWitnessGuard.generatorGuard_correct z).1 h
  simp [templateWorker,TM2CircuitTemplate.build_correct,TM2BoundedUnary.expand_guarded z.1.2 z.2 hb,intended]

/-- The conditional interface is reduced to only output-wire and gate-list
construction; the template is supplied by a compiled machine. -/
theorem circuitData_of_gateData (h : GateDataPolyTime) : CircuitDataPolyTime := by
  intro program
  obtain ⟨F,hF,hcorrect⟩ := h program
  refine ⟨fun z => (templateWorker program z,F z),
    TM2GuardAllStep.pair_isPolyTime (templateWorker program) F (templateWorker_isPolyTime program) hF,?_⟩
  intro z hz
  change (templateWorker program z,F z) = intended program z
  rw [templateWorker_correct program z hz,hcorrect z hz]
  exact Prod.eta (intended program z)

theorem pnp_exists_of_gateData (h : GateDataPolyTime) :
    ∃ c : Turing.ToPartrec.Code, (Shared.Beeping.ControllerBinary.machine c).system.EventuallySilent ↔
      ComplexityTheory.P = ComplexityTheory.NP :=
  pnp_exists_of_circuitData (circuitData_of_gateData h)

theorem npconp_exists_of_gateData (h : GateDataPolyTime) :
    ∃ c : Turing.ToPartrec.Code, (Shared.Beeping.ControllerBinary.machine c).system.EventuallySilent ↔
      ComplexityTheory.NP = ComplexityTheory.coNP :=
  npconp_exists_of_circuitData (circuitData_of_gateData h)
end Shared.ComplexityBridge.GeneratorTemplateBridge
