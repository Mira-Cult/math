import Shared.ComplexityBridge.TM2PatchRefs
import Shared.ComplexityBridge.TM2BoundedCircuitWorker

set_option backward.isDefEq.respectTransparency false

/-! Exact polynomial-time witness circuit gate producer with explicit unary
witness size and clock, including the outer relocation. -/
namespace Shared.ComplexityBridge.TM2WitnessGateWorker
open Shared.ComplexityBridge
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTotalize
open Shared.ComplexityBridge.CircuitCNF

abbrev Input := TM2CircuitOutputWorker.Input

def window (z : Input) : List Bool := TM2CircuitOutputWorker.windowTokens z
def count (z : Input) : List Bool := TM2CircuitOutputWorker.countTokens z
def width (program : Program) (z : Input) : List Bool := TM2ProgramUnroll.widthTokens (totalProgram program) (window z)
def start (program : Program) (z : Input) : List Bool :=
  TM2CircuitOutputWorker.constantTokens (totalProgram program).length z.1.1 ++ window z ++ z.1.1

def patch (program : Program) (z : Input) : List Nat := TM2PatchRefs.patch (width program z,(start program z,count z))
def base (program : Program) (z : Input) : Nat := (width program z).length+(count z).length

def request (program : Program) (z : Input) : TM2CircuitCopy.Input :=
  ((width program z,base program z),((patch program z,TM2BoundedCircuitWorker.gates program z),[]))

def worker (program : Program) (z : Input) : List Gate := (TM2CircuitCopy.copy (request program z)).1

theorem worker_isPolyTime (program : Program) : ComplexityTheory.IsPolyTime (worker program) := by
  let pair : Input → List Bool × List Bool := fun z => z.1
  let pub : Input → List Bool := fun z => z.1.1
  let witness : Input → List Bool := fun z => z.1.2
  let win : Input → List Bool := window
  let cnt : Input → List Bool := count
  let wid : Input → List Bool := width program
  let constant : Input → List Bool := fun z => TM2CircuitOutputWorker.constantTokens (totalProgram program).length (pub z)
  let st : Input → List Bool := start program
  let patchArgs : Input → TM2PatchRefs.Context := fun z => (wid z,(st z,cnt z))
  let wires : Input → List Nat := patch program
  let widLen : Input → Nat := fun z => (wid z).length
  let cntLen : Input → Nat := fun z => (cnt z).length
  let b : Input → Nat := base program
  let gates : Input → List Gate := TM2BoundedCircuitWorker.gates program
  let empty : Input → List Nat := fun _ => []
  let req : Input → TM2CircuitCopy.Input := request program
  let copied : Input → List Gate × List Nat := fun z => TM2CircuitCopy.copy (req z)
  have hp : ComplexityTheory.IsPolyTime pair := TM2PairFirst.first_isPolyTime
  have hpub : ComplexityTheory.IsPolyTime pub := TM2Compose.isPolyTime_comp pair (fun p : List Bool × List Bool => p.1) hp TM2PairFirst.first_isPolyTime
  have hwitness : ComplexityTheory.IsPolyTime witness := TM2Compose.isPolyTime_comp pair (fun p : List Bool × List Bool => p.2) hp TM2GuardAllStep.second_isPolyTime
  have hwin : ComplexityTheory.IsPolyTime win := TM2TapeWorker.windowTokens_isPolyTime
  have hcnt : ComplexityTheory.IsPolyTime cnt := TM2Compose.isPolyTime_comp witness (TM2CircuitOutputWorker.copies 3) hwitness (TM2CircuitOutputWorker.copies_isPolyTime 3)
  have hwid : ComplexityTheory.IsPolyTime wid := TM2Compose.isPolyTime_comp win (TM2ProgramUnroll.widthTokens (totalProgram program)) hwin (TM2ProgramUnroll.widthTokens_isPolyTime _)
  have hconst : ComplexityTheory.IsPolyTime constant := TM2Compose.isPolyTime_comp pub (TM2CircuitOutputWorker.constantTokens (totalProgram program).length)
    hpub (TM2CircuitOutputWorker.constantTokens_isPolyTime _)
  have hst : ComplexityTheory.IsPolyTime st := TM2CircuitTemplate.append_isPolyTime (fun z => constant z++win z) pub
    (TM2CircuitTemplate.append_isPolyTime constant win hconst hwin) hpub
  have hpatchArgs : ComplexityTheory.IsPolyTime patchArgs := TM2GuardAllStep.pair_isPolyTime wid (fun z => (st z,cnt z)) hwid
    (TM2GuardAllStep.pair_isPolyTime st cnt hst hcnt)
  have hwires : ComplexityTheory.IsPolyTime wires := TM2Compose.isPolyTime_comp patchArgs TM2PatchRefs.patch hpatchArgs TM2PatchRefs.patch_isPolyTime
  have hwl : ComplexityTheory.IsPolyTime widLen := TM2Compose.isPolyTime_comp wid List.length hwid TM2BinaryListLength.length_isPolyTime
  have hcl : ComplexityTheory.IsPolyTime cntLen := TM2Compose.isPolyTime_comp cnt List.length hcnt TM2BinaryListLength.length_isPolyTime
  have hbase : ComplexityTheory.IsPolyTime b := TM2Compose.isPolyTime_comp (fun z => (widLen z,cntLen z)) CNFBinaryPairAdd.addPair
    (TM2GuardAllStep.pair_isPolyTime widLen cntLen hwl hcl) CNFBinaryPairAdd.addPair_isPolyTime
  have hg : ComplexityTheory.IsPolyTime gates := (TM2BoundedCircuitWorker.workers_isPolyTime program).1
  have he : ComplexityTheory.IsPolyTime empty := TM2EmptyConstant.isPolyTime [] rfl
  have hreq : ComplexityTheory.IsPolyTime req := TM2GuardAllStep.pair_isPolyTime (fun z => (wid z,b z))
    (fun z => ((wires z,gates z),empty z)) (TM2GuardAllStep.pair_isPolyTime wid b hwid hbase)
    (TM2GuardAllStep.pair_isPolyTime (fun z => (wires z,gates z)) empty (TM2GuardAllStep.pair_isPolyTime wires gates hwires hg) he)
  have hcopy : ComplexityTheory.IsPolyTime copied := TM2Compose.isPolyTime_comp req TM2CircuitCopy.copy hreq TM2CircuitCopy.copy_isPolyTime
  exact TM2Compose.isPolyTime_comp copied (fun p : List Gate × List Nat => p.1) hcopy TM2PairFirst.first_isPolyTime

theorem worker_correct (program : Program) (pub witness fuel : List Bool) :
    worker program ((pub,witness),fuel) = CircuitWitness.witnessGates program pub (3*witness.length) fuel.length := by
  let z : Input := ((pub,witness),fuel)
  let dummy := CircuitWitness.dummyInput pub (3*witness.length)
  let wid := width program z
  let st := start program z
  let cnt := count z
  let gs := TM2BoundedCircuitWorker.gates program z
  have hwin : (window z).length = CircuitBounded.window dummy fuel.length := by
    simp [window,z,TM2CircuitOutputWorker.windowTokens,TM2CircuitOutputWorker.countTokens,
      TM2CircuitOutputWorker.copies_length,CircuitBounded.window,dummy,CircuitWitness.dummyInput,Nat.add_assoc]
  have hcount : cnt.length = 3*witness.length := by simp [cnt,count,z,TM2CircuitOutputWorker.countTokens,TM2CircuitOutputWorker.copies_length]
  have hwidth : wid.length = CircuitWitness.innerWidth program pub (3*witness.length) fuel.length := by
    simp [wid,width,TM2ProgramUnroll.widthTokens_length,hwin,CircuitWitness.innerWidth,CircuitBounded.circuitWidth,dummy]
  have hstart : st.length = CircuitWitness.witnessStart program pub (3*witness.length) fuel.length := by
    simp [st,start,z,TM2CircuitOutputWorker.constantTokens_length,hwin,CircuitWitness.witnessStart,
      CircuitWitness.inputStart,dummy,Nat.add_assoc]
  have hbound : st.length ≤ wid.length := by
    rw [hstart,hwidth]
    have h := CircuitWitness.witnessEnd_bound program pub (3*witness.length) fuel.length
    exact Nat.le_trans (Nat.le_add_right _ _) h
  have hpatch : TM2PatchRefs.patch (wid,(st,cnt)) = CircuitWitness.refs program pub (3*witness.length) fuel.length := by
    rw [TM2PatchRefs.patch_correct wid st cnt hbound,hwidth,hstart,hcount]
    rfl
  have hgates : gs = CircuitBounded.circuitGates program dummy fuel.length := (TM2BoundedCircuitWorker.workers_correct program pub witness fuel).1
  have hv : validGates wid.length gs := by
    rw [hwidth,hgates]
    exact CircuitBounded.circuitGates_valid program dummy fuel.length
  have hcopy := TM2CircuitCopy.copy_correct wid (wid.length+cnt.length)
    (TM2PatchRefs.patch (wid,(st,cnt))) gs [] hv (by simp)
  have h := congrArg Prod.fst hcopy
  simpa [worker,request,base,patch,z,wid,st,cnt,gs,hwidth,hcount,hpatch,hgates,CircuitWitness.witnessGates,CircuitWitness.innerWidth,dummy] using h

namespace Fixtures
example : worker [] (([],[]),[]) = [] := rfl
end Fixtures
end Shared.ComplexityBridge.TM2WitnessGateWorker
