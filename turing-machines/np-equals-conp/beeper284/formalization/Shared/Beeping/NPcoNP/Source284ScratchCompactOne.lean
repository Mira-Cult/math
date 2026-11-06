import Shared.Beeping.NPcoNP.Source284ScratchFlipReturn
import Shared.Beeping.NPcoNP.Source284SourceRelocation

/-! A finite in-place pass moves a self-delimited witness stream one cell
toward a known zero gap cell. It does not yet autonomously remove the entire
gap or construct the verifier pair. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284ScratchCompactOne

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped push)

/-- States 0--3 move the zero boundary across a payload bit; states 4--6
move it across a one marker. A zero marker dispatches to the paid return. -/
def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,false,some 1⟩
  else if q = 1 then ⟨false,true,some (2+bit b)⟩
  else if q = 2 then ⟨false,true,some 4⟩
  else if q = 3 then ⟨true,true,some 4⟩
  else if q = 4 then ⟨b,false,some 5⟩
  else if q = 5 then ⟨false,true,some (if b then 6 else 7)⟩
  else if q = 6 then ⟨true,true,some 0⟩
  else if q = 7 then ⟨b,true,some 8⟩
  else shiftRow 8 (Source284ScratchFlipReturn.table continuation (q-8) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (14+states) (table continuation) := by
  have hc := Source284ScratchFlipReturn.closed states continuation hn hv
  intro q hq b q' hnext
  by_cases hs : q < 8
  · interval_cases q <;> cases b <;> simp [table,bit] at hnext <;> omega
  · have ht : (shiftRow 8 (Source284ScratchFlipReturn.table continuation (q-8) b)).next = some q' := by
      simpa [table,show q ≠ 0 by omega,show q ≠ 1 by omega,show q ≠ 2 by omega,
        show q ≠ 3 by omega,show q ≠ 4 by omega,show q ≠ 5 by omega,
        show q ≠ 6 by omega,show q ≠ 7 by omega] using hnext
    cases he : (Source284ScratchFlipReturn.table continuation (q-8) b).next with
    | none => simp [shiftRow,he] at ht
    | some r =>
      have h := hc (q-8) (by omega) b r he
      simp [shiftRow,he] at ht
      subst q'; omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (8+q) b = shiftRow 8 (Source284ScratchFlipReturn.table continuation q b) := by
  simp [table,show 8+q ≠ 1 by omega,show 8+q ≠ 2 by omega,show 8+q ≠ 3 by omega,
    show 8+q ≠ 4 by omega,show 8+q ≠ 5 by omega,show 8+q ≠ 6 by omega,show 8+q ≠ 7 by omega]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 8 c) =
      shiftConfig 8 (step (Source284ScratchFlipReturn.table continuation) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 8 c) fuel =
      shiftConfig 8 (run (Source284ScratchFlipReturn.table continuation) c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

/-- One actual six-transition pass shifts a payload/one pair across the
zero gap; the next zero gap lies immediately after the moved pair. -/
theorem payload_pair (continuation : Nat → Bool → Row) (left tail : Nat) (b : Bool) :
    run (table continuation) ⟨left,2*(bit b+2+4*tail),some 0⟩ 6 =
      ⟨4*left+2*bit b+1,2*tail,some 0⟩ := by
  have h0 : step (table continuation) ⟨left,2*(bit b+2+4*tail),some 0⟩ =
      ⟨2*left,bit b+2+4*tail,some 1⟩ := by
    cases b <;> simp [step,table,bit,Nat.testBit_zero] <;> omega
  have h1 : step (table continuation) ⟨2*left,bit b+2+4*tail,some 1⟩ =
      ⟨2+4*tail,2*left,some (2+bit b)⟩ := by
    cases b <;> simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega
  have h2 : step (table continuation) ⟨2+4*tail,2*left,some (2+bit b)⟩ =
      ⟨2*left+bit b,2+4*tail,some 4⟩ := by
    cases b <;> simp [step,table,bit,Nat.testBit_zero] <;> omega
  have h3 : step (table continuation) ⟨2*left+bit b,2+4*tail,some 4⟩ =
      ⟨4*left+2*bit b,1+2*tail,some 5⟩ := by
    cases b <;> simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega
  have h4 : step (table continuation) ⟨4*left+2*bit b,1+2*tail,some 5⟩ =
      ⟨2*tail,4*left+2*bit b,some 6⟩ := by
    cases b <;> simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega
  have h5 : step (table continuation) ⟨2*tail,4*left+2*bit b,some 6⟩ =
      ⟨4*left+2*bit b+1,2*tail,some 0⟩ := by
    cases b <;> simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega
  simp only [run,h0,h1,h2,h3,h4,h5]

theorem payload_pairs (continuation : Nat → Bool → Row) (w : List Bool) (left tail : Nat) :
    run (table continuation) ⟨left,2*flipped w tail,some 0⟩ (6*w.length) =
      ⟨push left w,2*flipped [] tail,some 0⟩ := by
  induction w generalizing left with
  | nil => rfl
  | cons b bs ih =>
    have ht : 6*(b::bs).length = 6+6*bs.length := by simp; omega
    rw [ht,run_add]
    change run (table continuation)
      (run (table continuation) ⟨left,2*(bit b+2+4*flipped bs tail),some 0⟩ 6) _ = _
    rw [payload_pair,ih]
    rfl

/-- The zero/zero terminator selects the return, without consulting the
arbitrary higher suffix. -/
theorem terminator (continuation : Nat → Bool → Row) (left tail : Nat) :
    run (table continuation) ⟨left,8*tail,some 0⟩ 6 =
      shiftConfig 8 ⟨4*left,2*tail,some 0⟩ := by
  have h0 : step (table continuation) ⟨left,8*tail,some 0⟩ = ⟨2*left,4*tail,some 1⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.mul_mod] <;> omega
  have h1 : step (table continuation) ⟨2*left,4*tail,some 1⟩ = ⟨4*tail,2*left,some 2⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.mul_mod] <;> omega
  have h2 : step (table continuation) ⟨4*tail,2*left,some 2⟩ = ⟨2*left,4*tail,some 4⟩ := by
    simp [step,table,bit,Nat.testBit_zero] <;> omega
  have h3 : step (table continuation) ⟨2*left,4*tail,some 4⟩ = ⟨4*left,2*tail,some 5⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.mul_mod] <;> omega
  have h4 : step (table continuation) ⟨4*left,2*tail,some 5⟩ = ⟨2*tail,4*left,some 7⟩ := by
    simp [step,table,bit,Nat.testBit_zero] <;> omega
  have h5 : step (table continuation) ⟨2*tail,4*left,some 7⟩ = ⟨4*left,2*tail,some 8⟩ := by
    apply Source284WindowRewind.generic_turn; intro b; simp [table]
  simp only [run,h0,h1,h2,h3,h4,h5,shiftConfig,Option.map_some]

/-- If the cell before the boundary is zero, the same finite source table
consumes that gap cell and moves the entire witness stream one cell toward the
input. Both the full input-side data and the full high suffix are retained. -/
theorem compact (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate tail : Nat) :
    run (table continuation) ⟨2*certificate,2*flipped w tail,some 0⟩ (8*w.length+11) =
      ⟨certificate,2*flipped w (2*tail),some 14⟩ := by
  have ht : 8*w.length+11 = (6*w.length)+(6+(2*w.length+5)) := by omega
  rw [ht,run_add,payload_pairs,run_add]
  have he : 2*flipped [] tail = 8*tail := by simp [flipped]; omega
  rw [he]
  rw [terminator,relocated_run,Source284ScratchFlipReturn.return_frame]
  rfl

theorem compact_after (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate tail fuel : Nat) :
    run (table continuation) ⟨2*certificate,2*flipped w tail,some 0⟩ (8*w.length+11+fuel) =
      shiftConfig 14 (run continuation ⟨certificate,2*flipped w (2*tail),some 0⟩ fuel) := by
  rw [run_add,compact]
  change run (table continuation) (shiftConfig 8 (shiftConfig 6
    ⟨certificate,2*flipped w (2*tail),some 0⟩)) fuel = _
  rw [relocated_run,Source284ScratchFlipReturn.relocated_run,
    Source284SourceRelocation.shiftConfig_add]

namespace Fixtures
example (continuation : Nat → Bool → Row) :
    run (table continuation) ⟨14,0,some 0⟩ 11 = ⟨7,0,some 14⟩ := by
  simpa [flipped] using compact continuation [] 7 0

example (continuation : Nat → Bool → Row) :
    run (table continuation) ⟨14,150,some 0⟩ 27 = ⟨7,278,some 14⟩ := by
  simpa [flipped,bit] using compact continuation [true,false] 7 1
end Fixtures
end Shared.Beeping.NPcoNP.Source284ScratchCompactOne
