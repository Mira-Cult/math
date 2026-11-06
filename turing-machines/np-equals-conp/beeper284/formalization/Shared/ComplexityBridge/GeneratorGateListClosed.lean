import Shared.ComplexityBridge.TM2WitnessGateWorker
import Shared.ComplexityBridge.GeneratorGateListBridge

set_option backward.isDefEq.respectTransparency false

/-! Discharge the guarded witness-gate-list producer using the actual finite
polynomial-time circuit and relocation workers. This does not bind a concrete
beeping transition table or discharge unrelated model/refinement obligations. -/
namespace Shared.ComplexityBridge.GeneratorGateListClosed
open Shared.ComplexityBridge
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge.GeneratorCircuitBridge
open Shared.ComplexityBridge.GeneratorTemplateBridge
open Shared.ComplexityBridge.GeneratorGateListBridge

def worker (program : Program) (z : Input) : List CircuitCNF.Gate :=
  TM2WitnessGateWorker.worker program
    ((CircuitPairWitness.pairPrefix z.1.1.1,TM2BoundedUnary.expand (z.1.2,z.2)),z.1.1.2)

theorem worker_isPolyTime (program : Program) : ComplexityTheory.IsPolyTime (worker program) := by
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
  exact TM2Compose.isPolyTime_comp req (TM2WitnessGateWorker.worker program) hreq (TM2WitnessGateWorker.worker_isPolyTime program)

theorem worker_correct (program : Program) (z : Input) (h : TM2BoundedWitnessGuard.generatorGuard z = true) :
    worker program z = intendedGateList program z := by
  have hb := (TM2BoundedWitnessGuard.generatorGuard_correct z).1 h
  simp [worker,TM2WitnessGateWorker.worker_correct,TM2BoundedUnary.expand_guarded z.1.2 z.2 hb,
    intendedGateList,intendedGates,intended]

/-- Every fixed finite program has an everywhere-polynomial total producer
which returns its exact witness gates on all guarded requests. -/
theorem gateListPolyTime : GateListPolyTime := by
  intro program
  exact ⟨worker program,worker_isPolyTime program,worker_correct program⟩

/-- The complete bounded-formula family and its uniform SAT reduction are
implemented using the now-discharged guarded gate-list producer. -/
theorem generatorPolyTime : BoundedHardness.GeneratorPolyTime :=
  GeneratorUnaryFormula.generator_of_boundedFormula
    (GeneratorSafeBridge.boundedFormula_of_safe
      (GeneratorCircuitBridge.safeFormula_of_circuitData
        (GeneratorTemplateBridge.circuitData_of_gateData (gateData_of_gateList gateListPolyTime))))

theorem satHard : CNFWitness.SatHard :=
  FiniteVerifierCompiler.sat_hard_of_generator generatorPolyTime

/-- The actual all-bitstrings SAT front end is complete for the canonical
NP class, with its proved verifier and uniform many-one reductions. -/
noncomputable def satComplete : CanonicalClasses.CompleteLanguage CNF.sat :=
  TM2PreparedVerify.complete_of_sat_hard satHard

/-- A later literal-table binding may use either of these theorems once its
own comparison implementation certificate has been checked. -/
theorem pnp_of_certificate {n : Nat} {M : Shared.Beeping.Machines.Machine n}
    (cert : Shared.Beeping.ComparisonImplementation.Certificate Shared.PNP.TM2Candidate.compareSAT 0 M) :
    M.system.EventuallySilent ↔ ComplexityTheory.P = ComplexityTheory.NP :=
  TM2PreparedVerify.pnp_of_sat_hard cert satHard

theorem npconp_of_certificate {n : Nat} {M : Shared.Beeping.Machines.Machine n}
    (cert : Shared.Beeping.ComparisonImplementation.Certificate Shared.NPCONP.TM2Verifier.compare 0 M) :
    M.system.EventuallySilent ↔ ComplexityTheory.NP = ComplexityTheory.coNP :=
  TM2PreparedVerify.npconp_of_sat_hard cert satHard

theorem pnp_exists :
    ∃ c : Turing.ToPartrec.Code, (Shared.Beeping.ControllerBinary.machine c).system.EventuallySilent ↔
      ComplexityTheory.P = ComplexityTheory.NP :=
  pnp_exists_of_gateList gateListPolyTime

theorem npconp_exists :
    ∃ c : Turing.ToPartrec.Code, (Shared.Beeping.ControllerBinary.machine c).system.EventuallySilent ↔
      ComplexityTheory.NP = ComplexityTheory.coNP :=
  npconp_exists_of_gateList gateListPolyTime
end Shared.ComplexityBridge.GeneratorGateListClosed
