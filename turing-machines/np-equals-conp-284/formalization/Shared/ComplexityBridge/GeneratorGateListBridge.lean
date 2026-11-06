import Shared.ComplexityBridge.TM2CircuitOutputWorker
import Shared.ComplexityBridge.GeneratorTemplateBridge

/-! The output-wire worker is implemented; only the concrete witness gate
list remains as a conditional polynomial-time producer. -/
namespace Shared.ComplexityBridge.GeneratorGateListBridge
open Shared.ComplexityBridge
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge.CNF
open Shared.ComplexityBridge.CircuitCNF
open Shared.ComplexityBridge.GeneratorCircuitBridge
open Shared.ComplexityBridge.GeneratorTemplateBridge

def intendedGateList (program : Program) (z : Input) : List Gate := (intendedGates program z).2

def GateListPolyTime : Prop :=
  ∀ program : Program, ∃ F : Input → List Gate, ComplexityTheory.IsPolyTime F ∧
    ∀ z, TM2BoundedWitnessGuard.generatorGuard z = true → F z = intendedGateList program z

def outputWorker (program : Program) (z : Input) : Nat :=
  TM2CircuitOutputWorker.worker program
    ((CircuitPairWitness.pairPrefix z.1.1.1,TM2BoundedUnary.expand (z.1.2,z.2)),z.1.1.2)

theorem outputWorker_isPolyTime (program : Program) : ComplexityTheory.IsPolyTime (outputWorker program) := by
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
  have h := TM2Compose.isPolyTime_comp req (TM2CircuitOutputWorker.worker program) hreq (TM2CircuitOutputWorker.worker_isPolyTime program)
  change ComplexityTheory.IsPolyTime (fun z : Input => TM2CircuitOutputWorker.worker program
    ((CircuitPairWitness.pairPrefix z.1.1.1,TM2BoundedUnary.expand (z.1.2,z.2)),z.1.1.2))
  exact h


theorem outputWorker_correct (program : Program) (z : Input)
    (h : TM2BoundedWitnessGuard.generatorGuard z = true) :
    outputWorker program z = (intendedGates program z).1 := by
  have hb := (TM2BoundedWitnessGuard.generatorGuard_correct z).1 h
  simp [outputWorker,TM2CircuitOutputWorker.worker_correct,TM2BoundedUnary.expand_guarded z.1.2 z.2 hb,
    intendedGates,intended]

/-- The output wire is proved; the only remaining hypothesis here is the
finite polynomial-time producer for the actual gate list. -/
theorem gateData_of_gateList (h : GateListPolyTime) : GateDataPolyTime := by
  intro program
  obtain ⟨F,hF,hcorrect⟩ := h program
  refine ⟨fun z => (outputWorker program z,F z),
    TM2GuardAllStep.pair_isPolyTime (outputWorker program) F (outputWorker_isPolyTime program) hF,?_⟩
  intro z hz
  change (outputWorker program z,F z) = intendedGates program z
  rw [outputWorker_correct program z hz,hcorrect z hz]
  exact Prod.eta (intendedGates program z)

theorem pnp_exists_of_gateList (h : GateListPolyTime) :
    ∃ c : Turing.ToPartrec.Code, (Shared.Beeping.ControllerBinary.machine c).system.EventuallySilent ↔
      ComplexityTheory.P = ComplexityTheory.NP :=
  pnp_exists_of_gateData (gateData_of_gateList h)

theorem npconp_exists_of_gateList (h : GateListPolyTime) :
    ∃ c : Turing.ToPartrec.Code, (Shared.Beeping.ControllerBinary.machine c).system.EventuallySilent ↔
      ComplexityTheory.NP = ComplexityTheory.coNP :=
  npconp_exists_of_gateData (gateData_of_gateList h)
end Shared.ComplexityBridge.GeneratorGateListBridge
