import Shared.Beeping.NPcoNP.Source284ScratchShiftCycle

/-! Install a protected sentinel beside the arbitrary certificate using two
paid scratch shifts. The result supports unambiguous two-cell unary tokens;
no input-length comparison or runtime stopping rule is asserted here. -/
namespace Shared.Beeping.NPcoNP.Source284ScratchSentinel

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284Parser (payloadFold)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (push flipped)
open Shared.Beeping.NPcoNP.Source284ScratchShift (written)

theorem fold_written_any (left : Nat) (w : List Bool) :
    payloadFold left (written false w) = 2*push (2*left) w := by
  rw [Source284ScratchShift.written_eq]
  simpa [payloadFold] using Source284ScratchShiftReturn.fold_scratchPrefix (2*left) w

/-- The reverse pass also works when the protected left boundary is odd;
this permits a sentinel bit to sit immediately next to the certificate. -/
theorem return_any_left (continuation : Nat → Bool → Row) (w : List Bool)
    (left tail : Nat) :
    run (Source284ScratchShiftReturn.table continuation)
      ⟨2*(tail/2),payloadFold left (written false w),some 0⟩ (2*w.length+3) =
      ⟨left,2*flipped w (tail/2),some 7⟩ := by
  rw [fold_written_any]
  have ht : 2*w.length+3 = 1+(2*w.length+2) := by omega
  rw [ht,Source284PayloadPop.run_add]
  change run (Source284ScratchShiftReturn.table continuation)
    (step (Source284ScratchShiftReturn.table continuation)
      ⟨2*(tail/2),2*push (2*left) w,some 0⟩) _ = _
  rw [Source284ScratchShiftReturn.entry_step]
  have he : 2*(2*(tail/2)) = 4*(tail/2) := by omega
  rw [he]
  change run (Source284ScratchShiftReturn.table continuation)
    (shiftConfig 1 ⟨4*(tail/2),push (2*left) w,some 3⟩) _ = _
  rw [Source284ScratchShiftReturn.relocated_run]
  have hc : 2*w.length+2 = (2*w.length)+2 := by omega
  rw [hc,Source284ScratchFlipReturn.run_add,Source284ScratchFlipReturn.reverse_pairs,
    Source284ScratchFlipReturn.raw_flipped,Source284ScratchFlipReturn.finish]
  rfl

/-- The entry writes a sentinel one instead of crossing the old zero. The
following finite shifter makes a replacement zero before the stream. -/
def special (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨true,false,some 1⟩
  else shiftRow 1 (Source284ScratchShift.table (Source284ScratchShiftReturn.table continuation) (q-1) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (14+states) (special continuation) := by
  have hret := Source284ScratchShiftReturn.closed states continuation hn hv
  have hshift := Source284ScratchShift.closed (7+states) (Source284ScratchShiftReturn.table continuation)
    (by omega) hret
  intro q hq b q' hnext
  by_cases h0 : q = 0
  · subst q; simp [special] at hnext; omega
  · have ht : (shiftRow 1 (Source284ScratchShift.table
        (Source284ScratchShiftReturn.table continuation) (q-1) b)).next = some q' := by
      simpa [special,h0] using hnext
    have hq0 : q-1 < 6+(7+states) := by omega
    cases he : (Source284ScratchShift.table (Source284ScratchShiftReturn.table continuation) (q-1) b).next with
    | none => simp [shiftRow,he] at ht
    | some r =>
      have h := hshift (q-1) hq0 b r he
      simp [shiftRow,he] at ht
      subst q'
      omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    special continuation (1+q) b =
      shiftRow 1 (Source284ScratchShift.table (Source284ScratchShiftReturn.table continuation) q b) := by
  simp [special]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (special continuation) (shiftConfig 1 c) =
      shiftConfig 1 (step (Source284ScratchShift.table (Source284ScratchShiftReturn.table continuation)) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (special continuation) (shiftConfig 1 c) fuel =
      shiftConfig 1 (run (Source284ScratchShift.table (Source284ScratchShiftReturn.table continuation)) c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

theorem first_step (continuation : Nat → Bool → Row) (left right : Nat) :
    step (special continuation) ⟨left,2*right,some 0⟩ = ⟨2*left+1,right,some 1⟩ := by
  simp [step,special,bit,Nat.testBit_zero]

/-- One real pass installs a protected one immediately above the certificate
and restores a zero at the stream boundary. -/
theorem special_frame (continuation : Nat → Bool → Row) (w : List Bool) (certificate tail : Nat) :
    run (special continuation) ⟨certificate,2*flipped w tail,some 0⟩ (4*w.length+7) =
      ⟨2*certificate+1,2*flipped w (tail/2),some 14⟩ := by
  have ht : 4*w.length+7 = 1+((2*w.length+3)+(2*w.length+3)) := by omega
  rw [ht,Source284PayloadPop.run_add]
  change run (special continuation)
    (step (special continuation) ⟨certificate,2*flipped w tail,some 0⟩) _ = _
  rw [first_step]
  change run (special continuation) (shiftConfig 1 ⟨2*certificate+1,flipped w tail,some 0⟩) _ = _
  rw [relocated_run,Source284PayloadPop.run_add,Source284ScratchShift.shift]
  change shiftConfig 1 (run (Source284ScratchShift.table (Source284ScratchShiftReturn.table continuation))
    (shiftConfig 6 ⟨2*(tail/2),payloadFold (2*certificate+1) (written false w),some 0⟩) _) = _
  rw [Source284ScratchShift.relocated_run,return_any_left]
  rfl

/-- All later execution of the finite continuation is transported through
the sentinel pass with its actual fourteen-state offset. -/
theorem continuation_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (special continuation) (shiftConfig 14 c) fuel = shiftConfig 14 (run continuation c fuel) := by
  rw [← Source284ScratchShiftCycle.shift_nested c]
  rw [relocated_run,Source284ScratchShift.relocated_run,Source284ScratchShiftReturn.relocated_run,
    Source284ScratchFlipReturn.relocated_run,Source284ScratchShiftCycle.shift_nested]

/-- Two low-endian zero cells per unary token, followed by a `0,1`
sentinel and then the untouched arbitrary certificate. -/
def unaryPairs : Nat → List Bool
  | 0 => [false,true]
  | k+1 => false :: false :: unaryPairs k

theorem unaryPairs_length (k : Nat) : (unaryPairs k).length = 2*k+2 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [unaryPairs,ih]; omega

theorem unaryPairs_stack (k certificate : Nat) :
    Source284LoaderAlgebra.stack (unaryPairs k) certificate = 2^(2*k)*(4*certificate+2) := by
  induction k with
  | zero => simp [unaryPairs,Source284LoaderAlgebra.stack] <;> omega
  | succ k ih =>
    simp only [unaryPairs,Source284LoaderAlgebra.stack,ih,if_false]
    have he : 2*(k+1) = 2*k+2 := by omega
    rw [he,pow_add]
    norm_num
    ring

end Shared.Beeping.NPcoNP.Source284ScratchSentinel
