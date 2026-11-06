import Shared.Beeping.NPcoNP.Source284ScratchScanner

/-! A finite source scanner flips each scratch marker: payload/zero pairs
become payload/one pairs and the `0,1` terminator becomes `0,0`. The output
can therefore be recognized in reverse using the original zero boundary. -/
namespace Shared.Beeping.NPcoNP.Source284ScratchFlip

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284PayloadLoop (scratch)
open Shared.Beeping.NPcoNP.Source284ScratchTerminator (mark)

/-- Same three-state scanner as the preserving scanner, except each marker
is flipped while its value controls continuation or handoff. -/
def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,false,some 1⟩
  else if q = 1 then ⟨b,false,some 2⟩
  else if q = 2 then ⟨!b,false,some (if b then 3 else 1)⟩
  else shiftRow 3 (continuation (q-3) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (3+states) (table continuation) := by
  intro q hq b q' hnext
  by_cases h0 : q = 0
  · subst q; simp [table] at hnext; omega
  · by_cases h1 : q = 1
    · subst q; simp [table] at hnext; omega
    · by_cases h2 : q = 2
      · subst q; cases b <;> simp [table] at hnext <;> omega
      · have ht : (shiftRow 3 (continuation (q-3) b)).next = some q' := by
          simpa [table,h0,h1,h2] using hnext
        have hq0 : q-3 < states := by omega
        cases he : (continuation (q-3) b).next with
        | none => simp [shiftRow,he] at ht
        | some r =>
          have h := hv (q-3) hq0 b r he
          simp [shiftRow,he] at ht
          subst q'
          omega

def push : Nat → List Bool → Nat
  | left, [] => left
  | left, b::bs => push (4*left+2*bit b+1) bs

theorem initial (continuation : Nat → Bool → Row) (left right : Nat) :
    step (table continuation) ⟨left,2*right,some 0⟩ = ⟨2*left,right,some 1⟩ := by
  simp [step,table,bit,Nat.testBit_zero]

theorem payload_pair (continuation : Nat → Bool → Row) (left tail : Nat) (b : Bool) :
    run (table continuation) ⟨left,bit b+4*tail,some 1⟩ 2 =
      ⟨4*left+2*bit b+1,tail,some 1⟩ := by
  cases b <;> simp [run,step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;>
    congr 1 <;> try split_ifs <;> omega

theorem terminator (continuation : Nat → Bool → Row) (left tail : Nat) :
    run (table continuation) ⟨left,4*tail+2,some 1⟩ 2 =
      ⟨4*left,tail,some 3⟩ := by
  simp [run,step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;>
    congr 1 <;> try split_ifs <;> omega

theorem scan (continuation : Nat → Bool → Row) (w : List Bool) (left suffix : Nat) :
    run (table continuation) ⟨left,scratch w (mark suffix),some 1⟩ (2*w.length+2) =
      ⟨4*push left w,suffix/4,some 3⟩ := by
  induction w generalizing left with
  | nil => simpa [scratch,mark,push] using terminator continuation left (suffix/4)
  | cons b bs ih =>
    have ht : 2*(b::bs).length+2 = 2+(2*bs.length+2) := by simp; omega
    rw [ht,Source284ScratchScanner.run_add]
    change run (table continuation)
      (run (table continuation) ⟨left,bit b+4*scratch bs (mark suffix),some 1⟩ 2) _ = _
    rw [payload_pair,ih]
    rfl

theorem scan_initial (continuation : Nat → Bool → Row) (w : List Bool)
    (certificate suffix : Nat) :
    run (table continuation) ⟨certificate,2*scratch w (mark suffix),some 0⟩ (2*w.length+3) =
      ⟨4*push (2*certificate) w,suffix/4,some 3⟩ := by
  have ht : 2*w.length+3 = (2*w.length+2)+1 := by omega
  rw [ht,Source284HardwireTable.run_front,initial,scan]

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (3+q) b = shiftRow 3 (continuation q b) := by
  have h0 : 3+q ≠ 0 := by omega
  have h1 : 3+q ≠ 1 := by omega
  have h2 : 3+q ≠ 2 := by omega
  simp [table,h0,h1,h2]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 3 c) = shiftConfig 3 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (clock : Nat) :
    run (table continuation) (shiftConfig 3 c) clock = shiftConfig 3 (run continuation c clock) := by
  induction clock with
  | zero => rfl
  | succ clock ih => simp only [run,ih,relocated_step]

/-- The flipped scratch stream has payload/one pairs and a zero/zero
terminator, followed by the retained higher suffix. -/
def flipped : List Bool → Nat → Nat
  | [], tail => 4*tail
  | b::bs, tail => bit b+2+4*flipped bs tail

end Shared.Beeping.NPcoNP.Source284ScratchFlip
