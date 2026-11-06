import Shared.ComplexityBridge.TM2ProgramMove

set_option backward.isDefEq.respectTransparency false

/-! Polynomial construction of output wire lists for a fixed transition
program and unary tape window. -/
namespace Shared.ComplexityBridge.TM2ProgramOutputs
open Shared.ComplexityBridge
open Shared.ComplexityBridge.CircuitProgramMove
open Shared.Codes.FinitePrograms

abbrev Input := TM2ProgramMove.Input

def stateOutput (program : Program) (j : Nat) (p : Input) : Nat :=
  nextStateOutput program p.1.length p.2 j

/-- Each fixed state index has its own finite table-field selector; the
program and index are compile-time parameters, not runtime oracles. -/
theorem stateOutput_isPolyTime (program : Program) (j : Nat) : ComplexityTheory.IsPolyTime (stateOutput program j) := by
  let tokens : Input → List Bool := fun p => p.1
  let base : Input → Nat := fun p => p.2
  let k : Input → Nat := fun p => (tokens p).length
  let read : Input → Nat := fun p => k p+program.length
  let movement : Input → List CircuitCNF.Gate := TM2ProgramMove.move program
  let size : Input → Nat := fun p => (movement p).length
  let afterMove : Input → Nat := fun p => base p+size p
  let tableBase : Input → Nat := fun p => afterMove p+j*(2+4*program.length)
  let args : Input → Nat × Nat := fun p => (read p,tableBase p)
  have ht : ComplexityTheory.IsPolyTime tokens := TM2PairFirst.first_isPolyTime
  have hb : ComplexityTheory.IsPolyTime base := TM2GuardAllStep.second_isPolyTime
  have hk : ComplexityTheory.IsPolyTime k := TM2Compose.isPolyTime_comp tokens List.length ht TM2BinaryListLength.length_isPolyTime
  have hr : ComplexityTheory.IsPolyTime read := TM2Compose.isPolyTime_comp k (fun n => n+program.length) hk (TM2FixedRows.addFixed_isPolyTime _)
  have hm : ComplexityTheory.IsPolyTime movement := TM2ProgramMove.move_isPolyTime program
  have hs : ComplexityTheory.IsPolyTime size := TM2Compose.isPolyTime_comp movement List.length hm TM2BinaryListLength.length_isPolyTime
  have ha : ComplexityTheory.IsPolyTime afterMove := TM2Compose.isPolyTime_comp (fun p => (base p,size p)) CNFBinaryPairAdd.addPair
    (TM2GuardAllStep.pair_isPolyTime base size hb hs) CNFBinaryPairAdd.addPair_isPolyTime
  have htb : ComplexityTheory.IsPolyTime tableBase := TM2Compose.isPolyTime_comp afterMove (fun n => n+j*(2+4*program.length)) ha (TM2FixedRows.addFixed_isPolyTime _)
  have hargs : ComplexityTheory.IsPolyTime args := TM2GuardAllStep.pair_isPolyTime read tableBase hr htb
  have h := TM2Compose.isPolyTime_comp args (fun p => tableResult program p.1 (rowNextIs (0+j)) p.2) hargs
    (TM2ProgramMove.tableResult_isPolyTime program (rowNextIs (0+j)))
  have he : (fun p => tableResult program (args p).1 (rowNextIs (0+j)) (args p).2) = stateOutput program j := by
    funext p
    simp [args,tableBase,afterMove,size,movement,TM2ProgramMove.move,read,k,tokens,base,stateOutput,nextStateOutput,stateResult,readIndex,Nat.add_comm]
  rw [he] at h
  exact h

def statesFrom (program : Program) : Nat → Nat → Input → List Nat
  | _,0,_ => []
  | start,count+1,p => stateOutput program start p :: statesFrom program (start+1) count p

theorem statesFrom_isPolyTime (program : Program) (count start : Nat) : ComplexityTheory.IsPolyTime (statesFrom program start count) := by
  induction count generalizing start with
  | zero => exact TM2EmptyConstant.isPolyTime [] rfl
  | succ count ih =>
    have h := TM2Compose.isPolyTime_comp (fun p => (stateOutput program start p,statesFrom program (start+1) count p))
      (TM2ListAppend.cons (α := Nat)) (TM2GuardAllStep.pair_isPolyTime (stateOutput program start)
        (statesFrom program (start+1) count) (stateOutput_isPolyTime program start) (ih (start+1))) TM2ListAppend.cons_isPolyTime
    change ComplexityTheory.IsPolyTime (statesFrom program start (count+1)) at h
    exact h

theorem statesFrom_correct (program : Program) (start count : Nat) (p : Input) :
    statesFrom program start count p = (List.range' start count).map (nextStateOutput program p.1.length p.2) := by
  induction count generalizing start with
  | zero => simp [statesFrom]
  | succ count ih => simp [statesFrom,List.range'_succ,ih,stateOutput]

/-- Tape output indices refer to outputs of the moved circuit, so their
relocation is an arithmetic offset and does not inspect the input list. -/
theorem tapeOutput_closed (program : Program) (k base i : Nat) :
    programMoveOutput program k base i = base+2*(2+4*program.length)+4*i+4 := by
  unfold programMoveOutput
  have he : CircuitTapeMove.outputIndex k i = CircuitTapeMove.width k+(4*i+4) := by
    simp [CircuitTapeMove.outputIndex]
    omega
  rw [he,CircuitRelocate.remap_output]
  rw [show (controls program k base).length = 2*(2+4*program.length) by simp [controls,rowControls_length]]
  omega

def tapeOutput (program : Program) (p : Input × Nat) : Nat :=
  programMoveOutput program p.1.1.length p.1.2 p.2

theorem tapeOutput_isPolyTime (program : Program) : ComplexityTheory.IsPolyTime (tapeOutput program) := by
  let request : Input × Nat → Input := fun p => p.1
  let index : Input × Nat → Nat := fun p => p.2
  let base : Input × Nat → Nat := fun p => p.1.2
  let twice : Input × Nat → Nat := fun p => 2*index p
  let four : Input × Nat → Nat := fun p => 2*twice p
  let offset : Input × Nat → Nat := fun p => base p+(2*(2+4*program.length)+4)
  have hr : ComplexityTheory.IsPolyTime request := TM2PairFirst.first_isPolyTime
  have hi : ComplexityTheory.IsPolyTime index := TM2GuardAllStep.second_isPolyTime
  have hb : ComplexityTheory.IsPolyTime base := TM2Compose.isPolyTime_comp request (fun p : Input => p.2) hr TM2GuardAllStep.second_isPolyTime
  have ht : ComplexityTheory.IsPolyTime twice := TM2Compose.isPolyTime_comp index (fun n => 2*n) hi CNFBinaryIndex.double_isPolyTime
  have hf : ComplexityTheory.IsPolyTime four := TM2Compose.isPolyTime_comp twice (fun n => 2*n) ht CNFBinaryIndex.double_isPolyTime
  have ho : ComplexityTheory.IsPolyTime offset := TM2Compose.isPolyTime_comp base (fun n => n+(2*(2+4*program.length)+4)) hb (TM2FixedRows.addFixed_isPolyTime _)
  have h := TM2Compose.isPolyTime_comp (fun p => (offset p,four p)) CNFBinaryPairAdd.addPair
    (TM2GuardAllStep.pair_isPolyTime offset four ho hf) CNFBinaryPairAdd.addPair_isPolyTime
  have he : (fun p => CNFBinaryPairAdd.addPair (offset p,four p)) = tapeOutput program := by
    funext p
    simp only [tapeOutput,tapeOutput_closed,CNFBinaryPairAdd.addPair,offset,four,twice,index,base]
    omega
  rw [he] at h
  exact h

def outputs (program : Program) (p : Input) : List Nat :=
  statesFrom program 0 program.length p ++
    TM2ContextMapGeneric.contextMap (tapeOutput program) (p,TM2TapeMove.indices p.1)

theorem outputs_isPolyTime (program : Program) : ComplexityTheory.IsPolyTime (outputs program) := by
  let state : Input → List Nat := statesFrom program 0 program.length
  let tokens : Input → List Bool := fun p => p.1
  let indices : Input → List Nat := fun p => TM2TapeMove.indices (tokens p)
  let ident : Input → Input := id
  let args : Input → Input × List Nat := fun p => (ident p,indices p)
  let tape : Input → List Nat := fun p => TM2ContextMapGeneric.contextMap (tapeOutput program) (args p)
  have hs : ComplexityTheory.IsPolyTime state := statesFrom_isPolyTime program program.length 0
  have ht : ComplexityTheory.IsPolyTime tokens := TM2PairFirst.first_isPolyTime
  have hi : ComplexityTheory.IsPolyTime indices := TM2Compose.isPolyTime_comp tokens TM2TapeMove.indices ht TM2TapeMove.indices_isPolyTime
  have hid : ComplexityTheory.IsPolyTime ident := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have ha : ComplexityTheory.IsPolyTime args := TM2GuardAllStep.pair_isPolyTime ident indices hid hi
  have htp : ComplexityTheory.IsPolyTime tape := TM2Compose.isPolyTime_comp args (TM2ContextMapGeneric.contextMap (tapeOutput program)) ha
    (TM2ContextMapGeneric.contextMap_isPolyTime (tapeOutput program) (tapeOutput_isPolyTime program))
  have hp := TM2GuardAllStep.pair_isPolyTime state tape hs htp
  have h := TM2Compose.isPolyTime_comp (fun p => (state p,tape p)) (TM2ListAppend.append (α := Nat)) hp TM2ListAppend.append_isPolyTime
  change ComplexityTheory.IsPolyTime (outputs program) at h
  exact h

theorem outputs_correct (program : Program) (tokens : List Bool) (base : Nat) :
    outputs program (tokens,base) = continuingOutputs program tokens.length base := by
  simp [outputs,statesFrom_correct,List.range_eq_range',TM2ContextMapGeneric.contextMap,
    TM2TapeMove.indices,TM2UnaryRange.rangeFromTokens,tapeOutput,continuingOutputs,Nat.mul_comm,Nat.add_comm]
  congr 2 <;> omega

namespace Fixtures
example : outputs [] ([],0) = [8] := by decide
end Fixtures
end Shared.ComplexityBridge.TM2ProgramOutputs
