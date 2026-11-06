import Shared.Beeping.NPcoNP.Source284UnaryErase
import Shared.Beeping.NPcoNP.Source284NestedReturn
import Shared.Beeping.NPcoNP.Source284SourceRelocation

/-! Scan the inner unary block, erase the outer block and return, preserving
an arbitrary certificate and the scratch boundary. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace Shared.Beeping.NPcoNP.Source284NestedErase

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig run_front)
open Shared.Beeping.NPcoNP.Source284PayloadLoop (scratch)
open Shared.Beeping.NPcoNP.Source284ScratchScanner (push)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)

def enterMarker (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then shiftRow 1 (Source284UnaryErase.table continuation 1 b)
  else shiftRow 1 (Source284UnaryErase.table continuation (q-1) b)

def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨true,true,some 2⟩
  else shiftRow 1 (Source284ScratchScanner.table (enterMarker continuation) (q-1) b)

theorem marker_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    enterMarker continuation (1+q) b = shiftRow 1 (Source284UnaryErase.table continuation q b) := by
  simp [enterMarker]

theorem marker_step (continuation : Nat → Bool → Row) (c : Config) :
    step (enterMarker continuation) (shiftConfig 1 c) =
      shiftConfig 1 (step (Source284UnaryErase.table continuation) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,marker_row,shiftRow]
      split <;> rfl

theorem marker_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (enterMarker continuation) (shiftConfig 1 c) fuel =
      shiftConfig 1 (run (Source284UnaryErase.table continuation) c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,marker_step]

theorem marker_jump (continuation : Nat → Bool → Row) (left right fuel : Nat) :
    run (enterMarker continuation) ⟨left,right,some 0⟩ (fuel+1) =
      shiftConfig 1 (run (Source284UnaryErase.table continuation)
        ⟨left,right,some 1⟩ (fuel+1)) := by
  rw [run_front,run_front]
  have hs : step (enterMarker continuation) ⟨left,right,some 0⟩ =
      shiftConfig 1 (step (Source284UnaryErase.table continuation) ⟨left,right,some 1⟩) := by
    simp [step,enterMarker,shiftRow,shiftConfig]
    split <;> rfl
  rw [hs,marker_run]

theorem scanner_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (1+q) b =
      shiftRow 1 (Source284ScratchScanner.table (enterMarker continuation) q b) := by
  simp [table]

theorem scanner_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 1 c) =
      shiftConfig 1 (step (Source284ScratchScanner.table (enterMarker continuation)) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,scanner_row,shiftRow]
      split <;> rfl

theorem scanner_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 1 c) fuel =
      shiftConfig 1 (run (Source284ScratchScanner.table (enterMarker continuation)) c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,scanner_step]

/-- Paid scan to the outer block, retaining a boundary marker. -/
theorem scan (continuation : Nat → Bool → Row) (inner : List Bool)
    (outer stream : Nat) :
    run (table continuation) ⟨pairTape inner outer,2*stream,some 0⟩ (2*inner.length+3) =
      ⟨4*push (2*stream+1) inner+1,outer,some 4⟩ := by
  have ht : 2*inner.length+3 = 1+(2*inner.length+2) := by omega
  rw [ht,Source284ScratchScanner.run_add]
  change run (table continuation) (step (table continuation)
    ⟨pairTape inner outer,2*stream,some 0⟩) _ = _
  have hs : step (table continuation) ⟨pairTape inner outer,2*stream,some 0⟩ =
      shiftConfig 1 ⟨2*stream+1,pairTape inner outer,some 1⟩ := by
    simp [step,table,shiftConfig,bit,Nat.testBit_zero]
  rw [hs,scanner_run]
  have hm : Source284ScratchTerminator.mark (4*outer) = 4*outer+2 := by
    simp [Source284ScratchTerminator.mark]
  have hd : (4*outer)/4 = outer := by omega
  have hh := Source284ScratchScanner.scan (enterMarker continuation) inner (2*stream+1) (4*outer)
  rw [hm,hd] at hh
  change run (Source284ScratchScanner.table (enterMarker continuation))
    ⟨2*stream+1,pairTape inner outer,some 1⟩ _ = _ at hh
  rw [hh]
  rfl


theorem enter_closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) :
    Closed (8+states) (enterMarker continuation) := by
  have hm := Source284UnaryErase.closed states continuation hn hv
  intro q hq b q' hnext
  by_cases h0 : q=0
  · subst q
    have he : (shiftRow 1 (Source284UnaryErase.table continuation 1 b)).next = some q' := by
      simpa [enterMarker] using hnext
    cases hh : (Source284UnaryErase.table continuation 1 b).next with
    | none => simp [shiftRow,hh] at he
    | some r =>
      have hr := hm 1 (by omega) b r hh
      simp [shiftRow,hh] at he
      subst q'; omega
  · have he : (shiftRow 1 (Source284UnaryErase.table continuation (q-1) b)).next = some q' := by
      simpa [enterMarker,h0] using hnext
    cases hh : (Source284UnaryErase.table continuation (q-1) b).next with
    | none => simp [shiftRow,hh] at he
    | some r =>
      have hr := hm (q-1) (by omega) b r hh
      simp [shiftRow,hh] at he
      subst q'; omega

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) :
    Closed (12+states) (table continuation) := by
  have hs := Source284ScratchScanner.closed (8+states) (enterMarker continuation) (by omega)
    (enter_closed states continuation hn hv)
  intro q hq b q' hnext
  by_cases h0 : q=0
  · subst q; simp [table] at hnext; omega
  · have he : (shiftRow 1 (Source284ScratchScanner.table (enterMarker continuation) (q-1) b)).next = some q' := by
      simpa [table,h0] using hnext
    cases hh : (Source284ScratchScanner.table (enterMarker continuation) (q-1) b).next with
    | none => simp [shiftRow,hh] at he
    | some r =>
      have hr := hs (q-1) (by omega) b r hh
      simp [shiftRow,hh] at he
      subst q'; omega

/-- Erase the outer block; the inner block is retained across the head. -/
theorem erase_outer (continuation : Nat → Bool → Row) (inner outer : List Bool)
    (certificate stream : Nat) :
    run (table continuation) ⟨pairTape inner (pairTape outer certificate),2*stream,some 0⟩
      (2*inner.length+4*outer.length+8) =
    ⟨4^(outer.length+1)*certificate,4*push (2*stream+1) inner,some 12⟩ := by
  have ht : 2*inner.length+4*outer.length+8 = (2*inner.length+3)+(4*outer.length+5) := by omega
  rw [ht,Source284ScratchScanner.run_add,scan]
  change run (table continuation) (shiftConfig 1
    (shiftConfig 3 ⟨4*push (2*stream+1) inner+1,pairTape outer certificate,some 0⟩)) _ = _
  rw [scanner_run,Source284ScratchScanner.relocated_run]
  have hh := Source284UnaryErase.clear continuation outer certificate (2*push (2*stream+1) inner)
  have he : 4*outer.length+6 = 1+(4*outer.length+5) := by omega
  rw [he,Source284ScratchScanner.run_add] at hh
  change run (Source284UnaryErase.table continuation)
    (step (Source284UnaryErase.table continuation)
      ⟨pairTape outer certificate,2*(2*push (2*stream+1) inner),some 0⟩) _ = _ at hh
  rw [Source284UnaryErase.startup] at hh
  have hc : 4*outer.length+5 = (4*outer.length+4)+1 := by omega
  rw [hc,marker_jump,← hc]
  have hp : 2*(2*push (2*stream+1) inner)+1 = 4*push (2*stream+1) inner+1 := by omega
  rw [hp] at hh
  rw [hh]
  simp [shiftConfig]
  omega

theorem shift_nested (c : Config) :
    shiftConfig 1 (shiftConfig 3 (shiftConfig 1 (shiftConfig 7 c))) = shiftConfig 12 c := by
  cases c with
  | mk left right state => cases state <;> simp [shiftConfig] <;> omega

theorem continuation_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 12 c) fuel = shiftConfig 12 (run continuation c fuel) := by
  rw [← shift_nested c]
  rw [scanner_run,Source284ScratchScanner.relocated_run,marker_run,Source284UnaryErase.relocated_run,shift_nested]

/-- One finite table erases the outer region, restores the inner region, and
executes an arbitrary continuation. -/
theorem erase_then (continuation : Nat → Bool → Row) (m : Nat) (outer : List Bool)
    (certificate stream fuel : Nat) :
    run (table (Source284NestedReturn.table continuation))
      ⟨pairTape (List.replicate m false) (pairTape outer certificate),2*stream,some 0⟩
      (4*m+4*outer.length+12+fuel) =
    shiftConfig 22 (run continuation
      ⟨pairTape (List.replicate m false) (4^(outer.length+1)*certificate),2*stream,some 0⟩ fuel) := by
  have ht : 4*m+4*outer.length+12+fuel =
      (2*(List.replicate m false).length+4*outer.length+8)+((2*m+4)+fuel) := by simp; omega
  rw [ht,Source284ScratchScanner.run_add,erase_outer]
  change run (table (Source284NestedReturn.table continuation))
    (shiftConfig 12 ⟨4^(outer.length+1)*certificate,
      4*push (2*stream+1) (List.replicate m false),some 0⟩) _ = _
  rw [continuation_run,Source284ScratchScanner.run_add,Source284NestedReturn.restore]
  change shiftConfig 12 (run (Source284NestedReturn.table continuation)
    (shiftConfig 10 ⟨pairTape (List.replicate m false) (4^(outer.length+1)*certificate),2*stream,some 0⟩) fuel) = _
  rw [show shiftConfig 10 ⟨pairTape (List.replicate m false) (4^(outer.length+1)*certificate),2*stream,some 0⟩ =
      shiftConfig 2 (shiftConfig 1 (shiftConfig 7 ⟨pairTape (List.replicate m false) (4^(outer.length+1)*certificate),2*stream,some 0⟩)) by rfl]
  rw [Source284NestedReturn.relocated_run,Source284NestedReturn.return_run,Source284UnaryClear.relocated_run]
  repeat rw [Source284SourceRelocation.shiftConfig_add]

end Shared.Beeping.NPcoNP.Source284NestedErase
