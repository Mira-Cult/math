import Shared.ComplexityBridge.TM2FixedRows
import Shared.ComplexityBridge.CircuitProgramMove

set_option backward.isDefEq.respectTransparency false

/-! Relocate a fixed finite table-selector circuit into runtime wire indices.
The generated TM2 may depend on the fixed program and selected field. -/
namespace Shared.ComplexityBridge.TM2FixedTableBlock
open Shared.ComplexityBridge
open Shared.ComplexityBridge.CircuitCNF
open Shared.ComplexityBridge.CircuitProgramMove
open Shared.Codes.FinitePrograms

abbrev Input := Nat × Nat -- read wire, base wire

theorem constantNat_isPolyTime (n : Nat) : ComplexityTheory.IsPolyTime (fun _ : Input => n) := by
  have h := TM2Compose.isPolyTime_comp (fun _ : Input => (0 : Nat)) (fun x => x+n)
    TM2EmptyConstant.zero_isPolyTime (TM2FixedRows.addFixed_isPolyTime n)
  have he : (fun _ : Input => 0+n) = (fun _ : Input => n) := by simp
  rw [he] at h
  exact h

def wire (n i : Nat) (p : Input) : Nat :=
  CircuitRelocate.remap (n+1) p.2 (tableRefs n p.1) i

theorem wire_isPolyTime (n i : Nat) : ComplexityTheory.IsPolyTime (wire n i) := by
  by_cases h : i < n
  · have he : wire n i = (fun _ : Input => i) := by
      funext p
      simp only [wire,CircuitRelocate.remap,if_pos (show i < n+1 by omega)]
      exact tableRefs_state n p.1 i h
    rw [he]
    exact constantNat_isPolyTime i
  · by_cases heq : i = n
    · subst i
      have he : wire n n = (fun p : Input => p.1) := by
        funext p
        simp only [wire,CircuitRelocate.remap,if_pos (show n < n+1 by omega)]
        exact tableRefs_read n p.1
      rw [he]
      exact TM2PairFirst.first_isPolyTime
    · have he : wire n i = (fun p : Input => p.2+(i-(n+1))) := by
        funext p
        simp only [wire,CircuitRelocate.remap,if_neg (show ¬ i < n+1 by omega)]
      rw [he]
      exact TM2Compose.isPolyTime_comp (fun p : Input => p.2) (fun x => x+(i-(n+1)))
        TM2GuardAllStep.second_isPolyTime (TM2FixedRows.addFixed_isPolyTime _)

def gate (n : Nat) (g : Gate) (p : Input) : Gate :=
  CircuitRelocate.renameGate (CircuitRelocate.remap (n+1) p.2 (tableRefs n p.1)) g

theorem gate_isPolyTime (n : Nat) (g : Gate) : ComplexityTheory.IsPolyTime (gate n g) := by
  cases g with
  | constant b =>
    have h := TM2Compose.isPolyTime_comp (fun _ : Input => b) Gate.constant
      (TM2Constant.isPolyTime b) TM2BinaryListLength.constantGate_isPolyTime
    change ComplexityTheory.IsPolyTime (gate n (.constant b)) at h
    exact h
  | neg x =>
    have h := TM2Compose.isPolyTime_comp (wire n x) Gate.neg (wire_isPolyTime n x) TM2GateConstruct.neg_isPolyTime
    change ComplexityTheory.IsPolyTime (gate n (.neg x)) at h
    exact h
  | conj x y =>
    have hp := TM2GuardAllStep.pair_isPolyTime (wire n x) (wire n y) (wire_isPolyTime n x) (wire_isPolyTime n y)
    have h := TM2Compose.isPolyTime_comp (fun p => (wire n x p,wire n y p))
      (fun p : Nat × Nat => Gate.conj p.1 p.2) hp TM2GateConstruct.conj_isPolyTime
    change ComplexityTheory.IsPolyTime (gate n (.conj x y)) at h
    exact h
  | disj x y =>
    have hp := TM2GuardAllStep.pair_isPolyTime (wire n x) (wire n y) (wire_isPolyTime n x) (wire_isPolyTime n y)
    have h := TM2Compose.isPolyTime_comp (fun p => (wire n x p,wire n y p))
      (fun p : Nat × Nat => Gate.disj p.1 p.2) hp TM2GateConstruct.disj_isPolyTime
    change ComplexityTheory.IsPolyTime (gate n (.disj x y)) at h
    exact h

def relocate (n : Nat) (gs : List Gate) (p : Input) : List Gate :=
  CircuitRelocate.relocate (n+1) p.2 (tableRefs n p.1) gs

theorem relocate_isPolyTime (n : Nat) (gs : List Gate) : ComplexityTheory.IsPolyTime (relocate n gs) := by
  induction gs with
  | nil =>
    have h : ComplexityTheory.IsPolyTime (fun _ : Input => ([] : List Gate)) := TM2EmptyConstant.isPolyTime [] rfl
    change ComplexityTheory.IsPolyTime (relocate n []) at h
    exact h
  | cons g gs ih =>
    have hp := TM2GuardAllStep.pair_isPolyTime (gate n g) (relocate n gs) (gate_isPolyTime n g) ih
    have h := TM2Compose.isPolyTime_comp (fun p => (gate n g p,relocate n gs p))
      (TM2ListAppend.cons (α := Gate)) hp TM2ListAppend.cons_isPolyTime
    change ComplexityTheory.IsPolyTime (relocate n (g::gs)) at h
    exact h

/-- The exact relocated selector for a fixed finite program and row field. -/
theorem tableBlock_isPolyTime (program : Program) (project : Row → Bool) :
    ComplexityTheory.IsPolyTime (fun p : Input => tableBlock program p.1 project p.2) := by
  have h := relocate_isPolyTime program.length (CircuitTable.lookupGates program.length (CircuitTable.projectRows project program))
  change ComplexityTheory.IsPolyTime (fun p : Input => tableBlock program p.1 project p.2) at h
  exact h

/-- Both actual program control selectors, with the second offset derived from
the proved first-block length. -/
theorem rowControls_isPolyTime (program : Program) :
    ComplexityTheory.IsPolyTime (fun p : Input => rowControls program p.1 p.2) := by
  let first : Input → List Gate := fun p => tableBlock program p.1 rowWrite p.2
  let offset : Input → Nat := fun p => p.2+(2+4*program.length)
  let secondArgs : Input → Input := fun p => (p.1,offset p)
  let second : Input → List Gate := fun p => tableBlock program p.1 rowLeft (offset p)
  have hf : ComplexityTheory.IsPolyTime first := tableBlock_isPolyTime program rowWrite
  have hr : ComplexityTheory.IsPolyTime (fun p : Input => p.1) := TM2PairFirst.first_isPolyTime
  have hb : ComplexityTheory.IsPolyTime (fun p : Input => p.2) := TM2GuardAllStep.second_isPolyTime
  have ho : ComplexityTheory.IsPolyTime offset := TM2Compose.isPolyTime_comp (fun p : Input => p.2)
    (fun n => n+(2+4*program.length)) hb (TM2FixedRows.addFixed_isPolyTime _)
  have ha : ComplexityTheory.IsPolyTime secondArgs := TM2GuardAllStep.pair_isPolyTime (fun p => p.1) offset hr ho
  have hs : ComplexityTheory.IsPolyTime second := TM2Compose.isPolyTime_comp secondArgs
    (fun p => tableBlock program p.1 rowLeft p.2) ha (tableBlock_isPolyTime program rowLeft)
  have h := TM2RowGates.append_isPolyTime first second hf hs
  have he : (fun p => first p ++ second p) = (fun p : Input => rowControls program p.1 p.2) := by
    funext p
    simp only [first,second,offset,rowControls,tableBlock_length]
  rw [he] at h
  exact h

/-- Runtime window size and base are both charged by the finite machine. -/
theorem controls_isPolyTime (program : Program) :
    ComplexityTheory.IsPolyTime (fun p : Nat × Nat => controls program p.1 p.2) := by
  let window : Nat × Nat → Nat := fun p => p.1
  let base : Nat × Nat → Nat := fun p => p.2
  let read : Nat × Nat → Nat := fun p => window p+program.length
  let args : Nat × Nat → Input := fun p => (read p,base p)
  have hw : ComplexityTheory.IsPolyTime window := TM2PairFirst.first_isPolyTime
  have hb : ComplexityTheory.IsPolyTime base := TM2GuardAllStep.second_isPolyTime
  have hr : ComplexityTheory.IsPolyTime read := TM2Compose.isPolyTime_comp window
    (fun n => n+program.length) hw (TM2FixedRows.addFixed_isPolyTime _)
  have ha : ComplexityTheory.IsPolyTime args := TM2GuardAllStep.pair_isPolyTime read base hr hb
  have h := TM2Compose.isPolyTime_comp args (fun p => rowControls program p.1 p.2) ha (rowControls_isPolyTime program)
  have he : (fun p => rowControls program (args p).1 (args p).2) =
      (fun p : Nat × Nat => controls program p.1 p.2) := by
    funext p
    simp [args,read,window,base,controls,readIndex,Nat.add_comm]
  rw [he] at h
  exact h

namespace Fixtures
example : wire 3 1 (8,20) = 1 := rfl
example : wire 3 3 (8,20) = 8 := rfl
example : wire 3 6 (8,20) = 22 := rfl
end Fixtures
end Shared.ComplexityBridge.TM2FixedTableBlock
