import Shared.ComplexityBridge.TM2FixedStateGates
import Shared.ComplexityBridge.TM2TapeMove
import Shared.ComplexityBridge.TM2CircuitCopy
import Shared.ComplexityBridge.TM2TapeWorker

set_option backward.isDefEq.respectTransparency false

/-! Polynomial construction of the fixed program's wired tape transition.
The window is supplied in unary; the base is a binary natural. -/
namespace Shared.ComplexityBridge.TM2ProgramMove
open Shared.ComplexityBridge
open Shared.ComplexityBridge.CircuitCNF
open Shared.ComplexityBridge.CircuitProgramMove
open Shared.Codes.FinitePrograms

abbrev Input := List Bool × Nat

theorem tableResult_isPolyTime (program : Program) (project : Row → Bool) :
    ComplexityTheory.IsPolyTime (fun p : Nat × Nat => tableResult program p.1 project p.2) := by
  have h := TM2FixedTableBlock.wire_isPolyTime program.length
    (CircuitTable.lookupOutput program.length (CircuitTable.projectRows project program))
  change ComplexityTheory.IsPolyTime (fun p : Nat × Nat => tableResult program p.1 project p.2) at h
  exact h

theorem rowResults_isPolyTime (program : Program) :
    ComplexityTheory.IsPolyTime (fun p : Nat × Nat => (writeResult program p.1 p.2,leftResult program p.1 p.2)) := by
  let write : Nat × Nat → Nat := fun p => tableResult program p.1 rowWrite p.2
  let shifted : Nat × Nat → Nat := fun p => p.2+(2+4*program.length)
  let args : Nat × Nat → Nat × Nat := fun p => (p.1,shifted p)
  let left : Nat × Nat → Nat := fun p => tableResult program p.1 rowLeft (shifted p)
  have hw : ComplexityTheory.IsPolyTime write := tableResult_isPolyTime program rowWrite
  have hr : ComplexityTheory.IsPolyTime (fun p : Nat × Nat => p.1) := TM2PairFirst.first_isPolyTime
  have hb : ComplexityTheory.IsPolyTime (fun p : Nat × Nat => p.2) := TM2GuardAllStep.second_isPolyTime
  have hshift : ComplexityTheory.IsPolyTime shifted := TM2Compose.isPolyTime_comp (fun p : Nat × Nat => p.2)
    (fun n => n+(2+4*program.length)) hb (TM2FixedRows.addFixed_isPolyTime _)
  have ha : ComplexityTheory.IsPolyTime args := TM2GuardAllStep.pair_isPolyTime (fun p => p.1) shifted hr hshift
  have hl : ComplexityTheory.IsPolyTime left := TM2Compose.isPolyTime_comp args
    (fun p => tableResult program p.1 rowLeft p.2) ha (tableResult_isPolyTime program rowLeft)
  have h := TM2GuardAllStep.pair_isPolyTime write left hw hl
  have he : (fun p => (write p,left p)) = (fun p : Nat × Nat => (writeResult program p.1 p.2,leftResult program p.1 p.2)) := by
    funext p
    simp [write,left,shifted,writeResult,leftResult,tableBlock_length]
  rw [he] at h
  exact h

def refs (program : Program) (p : Input) : List Nat := tapeRefs program p.1.length p.2

/-- Exact tape references, including both table results, are generated from
runtime unary window tokens and a binary base. -/
theorem refs_isPolyTime (program : Program) : ComplexityTheory.IsPolyTime (refs program) := by
  let tokens : Input → List Bool := fun p => p.1
  let base : Input → Nat := fun p => p.2
  let window : Input → Nat := fun p => (tokens p).length
  let read : Input → Nat := fun p => window p+program.length
  let resultArgs : Input → Nat × Nat := fun p => (read p,base p)
  let controls : Input → Nat × Nat := fun p => (writeResult program (program.length+window p) (base p),leftResult program (program.length+window p) (base p))
  let first : Input → Nat := fun p => (controls p).1
  let second : Input → Nat := fun p => (controls p).2
  let indices : Input → List Nat := fun p => TM2TapeMove.indices (tokens p)
  let add : Nat → Nat := fun n => n+program.length
  let tail : Input → List Nat := fun p => (indices p).map add
  let last : Input → List Nat := fun p => second p::tail p
  have ht : ComplexityTheory.IsPolyTime tokens := TM2PairFirst.first_isPolyTime
  have hb : ComplexityTheory.IsPolyTime base := TM2GuardAllStep.second_isPolyTime
  have hw : ComplexityTheory.IsPolyTime window := TM2Compose.isPolyTime_comp tokens List.length ht TM2BinaryListLength.length_isPolyTime
  have hr : ComplexityTheory.IsPolyTime read := TM2Compose.isPolyTime_comp window (fun n => n+program.length) hw (TM2FixedRows.addFixed_isPolyTime _)
  have ha : ComplexityTheory.IsPolyTime resultArgs := TM2GuardAllStep.pair_isPolyTime read base hr hb
  have hc : ComplexityTheory.IsPolyTime controls := by
    have h := TM2Compose.isPolyTime_comp resultArgs (fun p => (writeResult program p.1 p.2,leftResult program p.1 p.2)) ha (rowResults_isPolyTime program)
    have he : (fun p => (writeResult program (resultArgs p).1 (resultArgs p).2,leftResult program (resultArgs p).1 (resultArgs p).2)) = controls := by
      funext p
      simp [resultArgs,read,controls,Nat.add_comm]
    rw [he] at h
    exact h
  have hf : ComplexityTheory.IsPolyTime first := TM2Compose.isPolyTime_comp controls (fun p : Nat × Nat => p.1) hc TM2PairFirst.first_isPolyTime
  have hs : ComplexityTheory.IsPolyTime second := TM2Compose.isPolyTime_comp controls (fun p : Nat × Nat => p.2) hc TM2GuardAllStep.second_isPolyTime
  have hi : ComplexityTheory.IsPolyTime indices := TM2Compose.isPolyTime_comp tokens TM2TapeMove.indices ht TM2TapeMove.indices_isPolyTime
  have hadd : ComplexityTheory.IsPolyTime add := TM2FixedRows.addFixed_isPolyTime _
  have hmap := TM2ContextMapGeneric.listMap_isPolyTime add hadd
  have htail : ComplexityTheory.IsPolyTime tail := TM2Compose.isPolyTime_comp indices (fun xs => xs.map add) hi hmap
  have hlast : ComplexityTheory.IsPolyTime last := TM2Compose.isPolyTime_comp (fun p => (second p,tail p))
    (TM2ListAppend.cons (α := Nat)) (TM2GuardAllStep.pair_isPolyTime second tail hs htail) TM2ListAppend.cons_isPolyTime
  have h := TM2Compose.isPolyTime_comp (fun p => (first p,last p)) (TM2ListAppend.cons (α := Nat))
    (TM2GuardAllStep.pair_isPolyTime first last hf hlast) TM2ListAppend.cons_isPolyTime
  have he : (fun p => TM2ListAppend.cons (first p,last p)) = refs program := by
    funext p
    simp [first,last,second,tail,indices,add,controls,window,tokens,base,refs,tapeRefs,readIndex,
      TM2TapeMove.indices,TM2UnaryRange.rangeFromTokens,TM2ListAppend.cons,Nat.mul_comm,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
    congr 2 <;> omega
  rw [he] at h
  exact h

def widthTokens (xs : List Bool) : List Bool :=
  TM2CircuitOutputWorker.constantTokens 3 xs ++ TM2CircuitOutputWorker.copies 2 xs

theorem widthTokens_length (xs : List Bool) : (widthTokens xs).length = CircuitTapeMove.width xs.length := by
  simp [widthTokens,TM2CircuitOutputWorker.constantTokens_length,TM2CircuitOutputWorker.copies_length,CircuitTapeMove.width]

theorem widthTokens_isPolyTime : ComplexityTheory.IsPolyTime widthTokens :=
  TM2CircuitTemplate.append_isPolyTime (TM2CircuitOutputWorker.constantTokens 3) (TM2CircuitOutputWorker.copies 2)
    (TM2CircuitOutputWorker.constantTokens_isPolyTime 3) (TM2CircuitOutputWorker.copies_isPolyTime 2)

def moveCopy (program : Program) (p : Input) : List Gate :=
  (TM2CircuitCopy.copy ((widthTokens p.1,p.2+2*(2+4*program.length)),
    ((refs program p,TM2TapeMove.moveGates p.1),[]))).1

theorem moveCopy_isPolyTime (program : Program) : ComplexityTheory.IsPolyTime (moveCopy program) := by
  let tokens : Input → List Bool := fun p => p.1
  let base : Input → Nat := fun p => p.2
  let wt : Input → List Bool := fun p => widthTokens (tokens p)
  let offset : Input → Nat := fun p => base p+2*(2+4*program.length)
  let wires : Input → List Nat := refs program
  let gates : Input → List Gate := fun p => TM2TapeMove.moveGates (tokens p)
  let empty : Input → List Nat := fun _ => []
  let args : Input → TM2CircuitCopy.Input := fun p => ((wt p,offset p),((wires p,gates p),empty p))
  let result : Input → List Gate × List Nat := fun p => TM2CircuitCopy.copy (args p)
  have ht : ComplexityTheory.IsPolyTime tokens := TM2PairFirst.first_isPolyTime
  have hb : ComplexityTheory.IsPolyTime base := TM2GuardAllStep.second_isPolyTime
  have hw : ComplexityTheory.IsPolyTime wt := TM2Compose.isPolyTime_comp tokens widthTokens ht widthTokens_isPolyTime
  have ho : ComplexityTheory.IsPolyTime offset := TM2Compose.isPolyTime_comp base (fun n => n+2*(2+4*program.length)) hb (TM2FixedRows.addFixed_isPolyTime _)
  have hr : ComplexityTheory.IsPolyTime wires := refs_isPolyTime program
  have hg : ComplexityTheory.IsPolyTime gates := TM2Compose.isPolyTime_comp tokens TM2TapeMove.moveGates ht TM2TapeMove.moveGates_isPolyTime
  have he : ComplexityTheory.IsPolyTime empty := TM2EmptyConstant.isPolyTime [] rfl
  have ha : ComplexityTheory.IsPolyTime args := TM2GuardAllStep.pair_isPolyTime (fun p => (wt p,offset p))
    (fun p => ((wires p,gates p),empty p)) (TM2GuardAllStep.pair_isPolyTime wt offset hw ho)
    (TM2GuardAllStep.pair_isPolyTime (fun p => (wires p,gates p)) empty (TM2GuardAllStep.pair_isPolyTime wires gates hr hg) he)
  have hc : ComplexityTheory.IsPolyTime result := TM2Compose.isPolyTime_comp args TM2CircuitCopy.copy ha TM2CircuitCopy.copy_isPolyTime
  have h := TM2Compose.isPolyTime_comp result (fun p : List Gate × List Nat => p.1) hc TM2PairFirst.first_isPolyTime
  change ComplexityTheory.IsPolyTime (moveCopy program) at h
  exact h

theorem moveCopy_correct (program : Program) (tokens : List Bool) (base : Nat) :
    moveCopy program (tokens,base) = CircuitRelocate.relocate (CircuitTapeMove.width tokens.length)
      (base+(controls program tokens.length base).length) (tapeRefs program tokens.length base)
      (CircuitTapeMove.moveGates tokens.length) := by
  have hv : validGates (widthTokens tokens).length (TM2TapeMove.moveGates tokens) := by
    simpa [widthTokens_length,TM2TapeMove.moveGates] using CircuitTapeMove.moveGates_valid tokens.length
  have h := TM2CircuitCopy.copy_correct (widthTokens tokens) (base+2*(2+4*program.length))
    (refs program (tokens,base)) (TM2TapeMove.moveGates tokens) [] hv (by simp)
  have hh := congrArg Prod.fst h
  simpa [moveCopy,widthTokens_length,refs,TM2TapeMove.moveGates,controls,rowControls_length] using hh

def move (program : Program) (p : Input) : List Gate := programMoveGates program p.1.length p.2

/-- Exact fixed-program transition movement block, for every unary window and
binary base, with all intermediate gate and wire data charged. -/
theorem move_isPolyTime (program : Program) : ComplexityTheory.IsPolyTime (move program) := by
  let tokens : Input → List Bool := fun p => p.1
  let base : Input → Nat := fun p => p.2
  let k : Input → Nat := fun p => (tokens p).length
  let args : Input → Nat × Nat := fun p => (k p,base p)
  let ctrl : Input → List Gate := fun p => controls program (k p) (base p)
  have ht : ComplexityTheory.IsPolyTime tokens := TM2PairFirst.first_isPolyTime
  have hb : ComplexityTheory.IsPolyTime base := TM2GuardAllStep.second_isPolyTime
  have hk : ComplexityTheory.IsPolyTime k := TM2Compose.isPolyTime_comp tokens List.length ht TM2BinaryListLength.length_isPolyTime
  have ha : ComplexityTheory.IsPolyTime args := TM2GuardAllStep.pair_isPolyTime k base hk hb
  have hc : ComplexityTheory.IsPolyTime ctrl := TM2Compose.isPolyTime_comp args (fun p => controls program p.1 p.2) ha (TM2FixedTableBlock.controls_isPolyTime program)
  have h := TM2RowGates.append_isPolyTime ctrl (moveCopy program) hc (moveCopy_isPolyTime program)
  have he : (fun p => ctrl p++moveCopy program p) = move program := by
    funext p
    simpa [ctrl,k,tokens,base,move,programMoveGates] using congrArg (fun gs => controls program p.1.length p.2 ++ gs) (moveCopy_correct program p.1 p.2)
  rw [he] at h
  exact h

def continuing (program : Program) (p : Input) : List Gate := continuingGates program p.1.length p.2

/-- The complete one-step transition gate list is generated in canonical
polynomial time for each fixed finite program. -/
theorem continuing_isPolyTime (program : Program) : ComplexityTheory.IsPolyTime (continuing program) := by
  let tokens : Input → List Bool := fun p => p.1
  let base : Input → Nat := fun p => p.2
  let k : Input → Nat := fun p => (tokens p).length
  let read : Input → Nat := fun p => k p+program.length
  let movement : Input → List Gate := move program
  let moveLen : Input → Nat := fun p => (movement p).length
  let offset : Input → Nat := fun p => base p+moveLen p
  let args : Input → Nat × Nat := fun p => (read p,offset p)
  let states : Input → List Gate := fun p => stateGates program (read p) (offset p) 0 program.length
  have ht : ComplexityTheory.IsPolyTime tokens := TM2PairFirst.first_isPolyTime
  have hb : ComplexityTheory.IsPolyTime base := TM2GuardAllStep.second_isPolyTime
  have hk : ComplexityTheory.IsPolyTime k := TM2Compose.isPolyTime_comp tokens List.length ht TM2BinaryListLength.length_isPolyTime
  have hr : ComplexityTheory.IsPolyTime read := TM2Compose.isPolyTime_comp k (fun n => n+program.length) hk (TM2FixedRows.addFixed_isPolyTime _)
  have hm : ComplexityTheory.IsPolyTime movement := move_isPolyTime program
  have hml : ComplexityTheory.IsPolyTime moveLen := TM2Compose.isPolyTime_comp movement List.length hm TM2BinaryListLength.length_isPolyTime
  have ho : ComplexityTheory.IsPolyTime offset := TM2Compose.isPolyTime_comp (fun p => (base p,moveLen p)) CNFBinaryPairAdd.addPair
    (TM2GuardAllStep.pair_isPolyTime base moveLen hb hml) CNFBinaryPairAdd.addPair_isPolyTime
  have ha : ComplexityTheory.IsPolyTime args := TM2GuardAllStep.pair_isPolyTime read offset hr ho
  have hs : ComplexityTheory.IsPolyTime states := TM2Compose.isPolyTime_comp args
    (fun p : Nat × Nat => stateGates program p.1 p.2 0 program.length) ha
    (TM2FixedStateGates.stateGates_isPolyTime program 0 program.length)
  have h := TM2RowGates.append_isPolyTime movement states hm hs
  have he : (fun p => movement p++states p) = continuing program := by
    funext p
    simp [movement,states,read,k,tokens,offset,base,moveLen,move,continuing,continuingGates,readIndex,Nat.add_comm]
  rw [he] at h
  exact h

namespace Fixtures
example : refs [] ([],0) = [1,3,0] := by decide
end Fixtures
end Shared.ComplexityBridge.TM2ProgramMove
