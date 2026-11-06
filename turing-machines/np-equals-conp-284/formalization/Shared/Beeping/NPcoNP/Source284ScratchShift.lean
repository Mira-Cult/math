import Shared.Beeping.NPcoNP.Source284ScratchFlipPipeline
import Shared.Beeping.NPcoNP.Source284LoaderAlgebra

/-! A fixed finite source table inserts one low cell into the self-delimiting
payload/one scratch stream. It carries each read bit in control and shifts the
finite stream by one position, overwriting one ignored high-suffix bit. The
new leftmost cell is zero. This is a local expansion primitive, not the full
canonical pair loader. -/
namespace Shared.Beeping.NPcoNP.Source284ScratchShift

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284Parser (payloadFold)

/-- States 0 and 1 read a data bit, carrying respectively zero or one.
States 2 and 3 read its marker. State 4 writes the final carried zero and
turns; state 5 is a continuing sink for malformed `1,0` terminators. -/
def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q < 2 then ⟨decide (q = 1),false,some (2+bit b)⟩
  else if q = 2 then ⟨false,false,some (if b then 1 else 4)⟩
  else if q = 3 then ⟨true,false,some (if b then 1 else 5)⟩
  else if q = 4 then ⟨false,true,some 6⟩
  else if q = 5 then ⟨b,false,some 5⟩
  else shiftRow 6 (continuation (q-6) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (6+states) (table continuation) := by
  intro q hq b q' hnext
  by_cases h0 : q < 2
  · cases b <;> simp [table,h0,bit] at hnext <;> omega
  · by_cases h2 : q = 2
    · subst q; cases b <;> simp [table] at hnext <;> omega
    · by_cases h3 : q = 3
      · subst q; cases b <;> simp [table] at hnext <;> omega
      · by_cases h4 : q = 4
        · subst q; simp [table] at hnext; omega
        · by_cases h5 : q = 5
          · subst q; simp [table] at hnext; omega
          · have ht : (shiftRow 6 (continuation (q-6) b)).next = some q' := by
              simpa [table,h0,h2,h3,h4,h5] using hnext
            have hq0 : q-6 < states := by omega
            cases he : (continuation (q-6) b).next with
            | none => simp [shiftRow,he] at ht
            | some r =>
              have h := hv (q-6) hq0 b r he
              simp [shiftRow,he] at ht
              subst q'
              omega

/-- Low-endian sequence written by the transducer before the final flush.
Its proof-level carry is a finite-state value, not an unbounded counter. -/
def written : Bool → List Bool → List Bool
  | carry, [] => [carry,false]
  | carry, b::bs => carry :: b :: written true bs

def scratchPrefix : List Bool → List Bool
  | [] => [false]
  | b::bs => b :: true :: scratchPrefix bs

theorem written_eq (carry : Bool) (w : List Bool) :
    written carry w = carry :: scratchPrefix w := by
  induction w generalizing carry with
  | nil => rfl
  | cons b bs ih => simp [written,scratchPrefix,ih]

/-- The list used in the shift statement is exactly the existing numeric
scratch stream, including its full two-zero terminator. -/
theorem flipped_stack (w : List Bool) (tail : Nat) :
    flipped w tail = Source284LoaderAlgebra.stack (scratchPrefix w ++ [false]) tail := by
  induction w with
  | nil => simp [flipped,scratchPrefix,Source284LoaderAlgebra.stack] <;> omega
  | cons b bs ih =>
    cases b <;> simp [flipped,scratchPrefix,Source284LoaderAlgebra.stack,bit,ih] <;> omega

theorem written_length (carry : Bool) (w : List Bool) :
    (written carry w).length = 2*w.length+2 := by
  induction w generalizing carry with
  | nil => rfl
  | cons b bs ih => simp [written,ih] <;> omega

/-- For initial zero carry, the finite data plus first delimiter zero have
been shifted one cell right. The omitted final delimiter zero is flushed by
the machine's last step. -/
theorem written_shift (w : List Bool) :
    written false w ++ [false] = false :: (scratchPrefix w ++ [false]) := by
  rw [written_eq]
  rfl

theorem pair (continuation : Nat → Bool → Row) (carry b : Bool) (left tail : Nat) :
    run (table continuation) ⟨left,bit b+2+4*tail,some (bit carry)⟩ 2 =
      ⟨4*left+2*bit carry+bit b,tail,some 1⟩ := by
  cases carry <;> cases b <;>
    simp [run,step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;>
    congr 1 <;> try split_ifs
  all_goals repeat' apply And.intro
  all_goals omega

theorem terminal (continuation : Nat → Bool → Row) (carry : Bool) (left tail : Nat) :
    run (table continuation) ⟨left,4*tail,some (bit carry)⟩ 2 =
      ⟨4*left+2*bit carry,tail,some 4⟩ := by
  cases carry <;>
    simp [run,step,table,bit,Nat.testBit_zero,Nat.mul_mod] <;>
    congr 1 <;> try split_ifs
  all_goals repeat' apply And.intro
  all_goals omega

/-- Each stream pair takes two actual source transitions; the zero/zero
terminator takes two more, including the empty payload case. -/
theorem scan (continuation : Nat → Bool → Row) (carry : Bool) (w : List Bool)
    (left tail : Nat) :
    run (table continuation) ⟨left,flipped w tail,some (bit carry)⟩ (2*w.length+2) =
      ⟨payloadFold left (written carry w),tail,some 4⟩ := by
  induction w generalizing carry left with
  | nil =>
    have h := terminal continuation carry left tail
    cases carry <;> simp [flipped,written,payloadFold,bit] at * <;>
      convert h using 1 <;> ring
  | cons b bs ih =>
    have ht : 2*(b::bs).length+2 = 2+(2*bs.length+2) := by simp; omega
    rw [ht,Source284PayloadPop.run_add]
    change run (table continuation)
      (run (table continuation) ⟨left,bit b+2+4*flipped bs tail,some (bit carry)⟩ 2) _ = _
    rw [pair]
    have h := ih true (4*left+2*bit carry+bit b)
    cases carry <;> cases b <;> simp [written,payloadFold,bit] at * <;>
      convert h using 1 <;> ring

theorem flush (continuation : Nat → Bool → Row) (left tail : Nat) :
    step (table continuation) ⟨left,tail,some 4⟩ = ⟨2*(tail/2),left,some 6⟩ := by
  simp [step,table,bit]

/-- The output is on the opposite side of the head after a real final write
and turn. The high suffix is preserved above its one overwritten low bit. -/
theorem shift (continuation : Nat → Bool → Row) (w : List Bool) (left tail : Nat) :
    run (table continuation) ⟨left,flipped w tail,some 0⟩ (2*w.length+3) =
      ⟨2*(tail/2),payloadFold left (written false w),some 6⟩ := by
  have ht : 2*w.length+3 = (2*w.length+2)+1 := by omega
  have h := scan continuation false w left tail
  change run (table continuation) ⟨left,flipped w tail,some 0⟩ (2*w.length+2) =
    ⟨payloadFold left (written false w),tail,some 4⟩ at h
  rw [ht,Source284PayloadPop.run_add,h]
  exact flush continuation _ _

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (6+q) b = shiftRow 6 (continuation q b) := by
  have h0 : ¬ 6+q < 2 := by omega
  have h2 : 6+q ≠ 2 := by omega
  have h3 : 6+q ≠ 3 := by omega
  have h4 : 6+q ≠ 4 := by omega
  have h5 : 6+q ≠ 5 := by omega
  simp [table,h0,h2,h3,h4,h5]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 6 c) = shiftConfig 6 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (clock : Nat) :
    run (table continuation) (shiftConfig 6 c) clock = shiftConfig 6 (run continuation c clock) := by
  induction clock with
  | zero => rfl
  | succ clock ih => simp only [run,ih,relocated_step]

end Shared.Beeping.NPcoNP.Source284ScratchShift
