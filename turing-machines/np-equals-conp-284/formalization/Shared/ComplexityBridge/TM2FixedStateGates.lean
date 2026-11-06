import Shared.ComplexityBridge.TM2FixedTableBlock

set_option backward.isDefEq.respectTransparency false

/-! Construct all next-state selectors for a fixed finite program. -/
namespace Shared.ComplexityBridge.TM2FixedStateGates
open Shared.ComplexityBridge
open Shared.ComplexityBridge.CircuitCNF
open Shared.ComplexityBridge.CircuitProgramMove
open Shared.Codes.FinitePrograms

abbrev Input := Nat × Nat -- read wire, base wire

/-- For each fixed program, start state, and number of state selectors, the
exact state-gate list is produced by a finite polynomial-time TM2. The
runtime read and base wire indices are included in the input cost. -/
theorem stateGates_isPolyTime (program : Program) (start count : Nat) :
    ComplexityTheory.IsPolyTime (fun p : Input => stateGates program p.1 p.2 start count) := by
  induction count generalizing start with
  | zero =>
    have h : ComplexityTheory.IsPolyTime (fun _ : Input => ([] : List Gate)) := TM2EmptyConstant.isPolyTime [] rfl
    change ComplexityTheory.IsPolyTime (fun p : Input => stateGates program p.1 p.2 start 0) at h
    exact h
  | succ count ih =>
    let first : Input → List Gate := fun p => tableBlock program p.1 (rowNextIs start) p.2
    let offset : Input → Nat := fun p => p.2+(2+4*program.length)
    let next : Input → Input := fun p => (p.1,offset p)
    let rest : Input → List Gate := fun p => stateGates program p.1 (offset p) (start+1) count
    have hf : ComplexityTheory.IsPolyTime first := TM2FixedTableBlock.tableBlock_isPolyTime program (rowNextIs start)
    have hr : ComplexityTheory.IsPolyTime (fun p : Input => p.1) := TM2PairFirst.first_isPolyTime
    have hb : ComplexityTheory.IsPolyTime (fun p : Input => p.2) := TM2GuardAllStep.second_isPolyTime
    have ho : ComplexityTheory.IsPolyTime offset := TM2Compose.isPolyTime_comp (fun p : Input => p.2)
      (fun x => x+(2+4*program.length)) hb (TM2FixedRows.addFixed_isPolyTime _)
    have hn : ComplexityTheory.IsPolyTime next := TM2GuardAllStep.pair_isPolyTime (fun p => p.1) offset hr ho
    have ht : ComplexityTheory.IsPolyTime rest := TM2Compose.isPolyTime_comp next
      (fun p : Input => stateGates program p.1 p.2 (start+1) count) hn (ih (start+1))
    have h := TM2RowGates.append_isPolyTime first rest hf ht
    change ComplexityTheory.IsPolyTime (fun p : Input => stateGates program p.1 p.2 start (count+1)) at h
    exact h

namespace Fixtures
example : stateGates ([] : Program) 0 3 0 0 = [] := rfl
end Fixtures
end Shared.ComplexityBridge.TM2FixedStateGates
