import Shared.Beeping.NPcoNP.Source284ScratchCompactOne

/-! A paid compacting pass that writes a one, rather than a zero, into the
high scratch cell created by removing one zero from the certificate side.
The protected framed payload and arbitrary remaining scratch are retained. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284ScratchCompactMarked

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped push)

def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 5 ∧ b = false then ⟨true,true,some 7⟩
  else Source284ScratchCompactOne.table continuation q b

theorem same_next (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    (table continuation q b).next = (Source284ScratchCompactOne.table continuation q b).next := by
  by_cases h : q=5 ∧ b=false
  · obtain ⟨rfl,rfl⟩ := h; rfl
  · simp [table,h]

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (14+states) (table continuation) := by
  intro q hq b q' hnext
  exact Source284ScratchCompactOne.closed states continuation hn hv q hq b q'
    (by simpa [same_next] using hnext)

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (8+q) b = shiftRow 8 (Source284ScratchFlipReturn.table continuation q b) := by
  simp [table,Source284ScratchCompactOne.relocated_row,show 8+q ≠ 5 by omega]

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

theorem payload_pair (continuation : Nat → Bool → Row) (left tail : Nat) (b : Bool) :
    run (table continuation) ⟨left,2*(bit b+2+4*tail),some 0⟩ 6 =
      ⟨4*left+2*bit b+1,2*tail,some 0⟩ := by
  have h0 : step (table continuation) ⟨left,2*(bit b+2+4*tail),some 0⟩ =
      ⟨2*left,bit b+2+4*tail,some 1⟩ := by
    cases b <;> simp [step,table,Source284ScratchCompactOne.table,bit,Nat.testBit_zero] <;> omega
  have h1 : step (table continuation) ⟨2*left,bit b+2+4*tail,some 1⟩ =
      ⟨2+4*tail,2*left,some (2+bit b)⟩ := by
    cases b <;> simp [step,table,Source284ScratchCompactOne.table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega
  have h2 : step (table continuation) ⟨2+4*tail,2*left,some (2+bit b)⟩ =
      ⟨2*left+bit b,2+4*tail,some 4⟩ := by
    cases b <;> simp [step,table,Source284ScratchCompactOne.table,bit,Nat.testBit_zero] <;> omega
  have h3 : step (table continuation) ⟨2*left+bit b,2+4*tail,some 4⟩ =
      ⟨4*left+2*bit b,1+2*tail,some 5⟩ := by
    cases b <;> simp [step,table,Source284ScratchCompactOne.table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega
  have h4 : step (table continuation) ⟨4*left+2*bit b,1+2*tail,some 5⟩ =
      ⟨2*tail,4*left+2*bit b,some 6⟩ := by
    cases b <;> simp [step,table,Source284ScratchCompactOne.table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega
  have h5 : step (table continuation) ⟨2*tail,4*left+2*bit b,some 6⟩ =
      ⟨4*left+2*bit b+1,2*tail,some 0⟩ := by
    cases b <;> simp [step,table,Source284ScratchCompactOne.table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega
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

theorem terminator (continuation : Nat → Bool → Row) (left tail : Nat) :
    run (table continuation) ⟨left,8*tail,some 0⟩ 6 =
      shiftConfig 8 ⟨4*left,2*tail+1,some 0⟩ := by
  have h0 : step (table continuation) ⟨left,8*tail,some 0⟩ = ⟨2*left,4*tail,some 1⟩ := by
    simp [step,table,Source284ScratchCompactOne.table,bit,Nat.testBit_zero,Nat.mul_mod] <;> omega
  have h1 : step (table continuation) ⟨2*left,4*tail,some 1⟩ = ⟨4*tail,2*left,some 2⟩ := by
    simp [step,table,Source284ScratchCompactOne.table,bit,Nat.testBit_zero,Nat.mul_mod] <;> omega
  have h2 : step (table continuation) ⟨4*tail,2*left,some 2⟩ = ⟨2*left,4*tail,some 4⟩ := by
    simp [step,table,Source284ScratchCompactOne.table,bit,Nat.testBit_zero] <;> omega
  have h3 : step (table continuation) ⟨2*left,4*tail,some 4⟩ = ⟨4*left,2*tail,some 5⟩ := by
    simp [step,table,Source284ScratchCompactOne.table,bit,Nat.testBit_zero,Nat.mul_mod] <;> omega
  have h4 : step (table continuation) ⟨4*left,2*tail,some 5⟩ = ⟨2*tail+1,4*left,some 7⟩ := by
    simp [step,table,Source284ScratchCompactOne.table,bit,Nat.testBit_zero] <;> omega
  have h5 : step (table continuation) ⟨2*tail+1,4*left,some 7⟩ = ⟨4*left,2*tail+1,some 8⟩ := by
    apply Source284WindowRewind.generic_turn; intro b; simp [table,Source284ScratchCompactOne.table]
  simp only [run,h0,h1,h2,h3,h4,h5,shiftConfig,Option.map_some]

theorem compact (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate tail : Nat) :
    run (table continuation) ⟨2*certificate,2*flipped w tail,some 0⟩ (8*w.length+11) =
      ⟨certificate,2*flipped w (2*tail+1),some 14⟩ := by
  have ht : 8*w.length+11 = (6*w.length)+(6+(2*w.length+5)) := by omega
  rw [ht,run_add,payload_pairs,run_add]
  have he : 2*flipped [] tail = 8*tail := by simp [flipped]; omega
  rw [he,terminator,relocated_run,Source284ScratchFlipReturn.return_frame]
  rfl

theorem compact_after (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate tail fuel : Nat) :
    run (table continuation) ⟨2*certificate,2*flipped w tail,some 0⟩ (8*w.length+11+fuel) =
      shiftConfig 14 (run continuation ⟨certificate,2*flipped w (2*tail+1),some 0⟩ fuel) := by
  rw [run_add,compact]
  change run (table continuation) (shiftConfig 8 (shiftConfig 6
    ⟨certificate,2*flipped w (2*tail+1),some 0⟩)) fuel = _
  rw [relocated_run,Source284ScratchFlipReturn.relocated_run,
    Source284SourceRelocation.shiftConfig_add]

namespace Fixtures
def loop (_ : Nat) (b : Bool) : Row := ⟨b,false,some 0⟩
example : run (table loop) ⟨14,0,some 0⟩ 11 = ⟨7,8,some 14⟩ := by decide +kernel
example : run (table loop) ⟨14,150,some 0⟩ 27 = ⟨7,406,some 14⟩ := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284ScratchCompactMarked
