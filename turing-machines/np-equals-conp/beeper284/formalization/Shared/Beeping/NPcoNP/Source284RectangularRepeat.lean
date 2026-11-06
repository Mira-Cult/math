import Shared.Beeping.NPcoNP.Source284SquareRepeat

/-! The existing finite nested-loop table also works for differently sized
token blocks. It preserves both blocks and an arbitrary certificate while
adding a fixed number of rectangular products to the scratch counter. It does
not convert that counter back to tokens or construct a raw-input runway. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284RectangularRepeat

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284CountedShift (counter)
open Shared.Beeping.NPcoNP.Source284TokenCounterLoop (halves)
open Shared.Beeping.NPcoNP.Source284SquareLoopTotal (loopCost)
open Shared.Beeping.NPcoNP.Source284SquareRepeat (round repeatTable)

def roundCost (outer inner current width : Nat) : Nat :=
  loopCost outer inner 0 current width+(4*inner+4*outer+12)

/-- One actual pass adds `outer*inner` counter marks and restores both token
blocks, including when either block is empty. -/
theorem round_then (continuation : Nat → Bool → Row) (outer inner current : Nat)
    (w : List Bool) (certificate higher fuel : Nat) :
    run (round continuation)
      ⟨pairTape (List.replicate inner false) (pairTape (List.replicate outer false) certificate),
        2*flipped w (counter current higher),some 0⟩
      (roundCost outer inner current w.length+fuel) =
    shiftConfig 110 (run continuation
      ⟨pairTape (List.replicate inner false) (pairTape (List.replicate outer false) certificate),
        2*flipped w (counter (current+outer*inner) (halves (outer*inner) higher)),some 0⟩ fuel) := by
  have ht : roundCost outer inner current w.length+fuel =
      loopCost outer inner 0 current w.length+
        ((4*inner+4*(List.replicate outer true).length+12)+fuel) := by
    simp [roundCost]; omega
  rw [ht]
  unfold Source284SquareRepeat.round
  have hl := Source284SquareLoopTotal.loop_then
    (Source284NestedReset.table (Source284NestedReturn.table continuation))
    outer inner 0 current w certificate higher
    ((4*inner+4*(List.replicate outer true).length+12)+fuel)
  simp only [List.replicate_zero,List.nil_append,Nat.zero_add] at hl
  rw [hl,Source284NestedReset.reset_then]
  simp only [List.length_replicate]
  rw [Source284SourceRelocation.shiftConfig_add]

def repeatCost : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _, _ => 0
  | k+1, outer, inner, current, width =>
      roundCost outer inner current width +
        repeatCost k outer inner (current+outer*inner) width

/-- For equal block lengths the generalized clock agrees exactly with the
previous square-loop clock. -/
theorem roundCost_square (n current width : Nat) :
    roundCost n n current width = Source284SquareRepeat.roundCost n current width := by
  simp only [roundCost,Source284SquareRepeat.roundCost]
  congr 1
  omega

theorem repeatCost_square (k n current width : Nat) :
    repeatCost k n n current width = Source284SquareRepeat.repeatCost k n current width := by
  induction k generalizing current with
  | zero => rfl
  | succ k ih =>
    simp only [repeatCost,Source284SquareRepeat.repeatCost,roundCost_square,ih]

/-- The pass count is fixed in the table; all inner and outer iterations are
controlled by their actual tape tokens. -/
theorem repeat_then (k : Nat) (continuation : Nat → Bool → Row)
    (outer inner current : Nat) (w : List Bool) (certificate higher fuel : Nat) :
    run (repeatTable k continuation)
      ⟨pairTape (List.replicate inner false) (pairTape (List.replicate outer false) certificate),
        2*flipped w (counter current higher),some 0⟩
      (repeatCost k outer inner current w.length+fuel) =
    shiftConfig (110*k) (run continuation
      ⟨pairTape (List.replicate inner false) (pairTape (List.replicate outer false) certificate),
        2*flipped w (counter (current+k*(outer*inner)) (halves (k*(outer*inner)) higher)),some 0⟩ fuel) := by
  induction k generalizing current higher with
  | zero => simp [repeatTable,repeatCost,shiftConfig,halves]
  | succ k ih =>
    have ht : repeatCost (k+1) outer inner current w.length+fuel =
        roundCost outer inner current w.length+
          (repeatCost k outer inner (current+outer*inner) w.length+fuel) := by
      simp [repeatCost]; omega
    rw [ht]
    change run (round (repeatTable k continuation)) _ _ = _
    rw [round_then,ih,Source284SourceRelocation.shiftConfig_add,
      Source284ReusableTokenIterations.halves_add]
    have ha : current+outer*inner+k*(outer*inner)=current+(k+1)*(outer*inner) := by ring
    have hb : k*(outer*inner)+outer*inner=(k+1)*(outer*inner) := by ring
    have hc : 110+110*k=110*(k+1) := by omega
    rw [ha,hb,hc]

/-- A nonnegative polynomial bound on one pass; no division or unit-cost
unbounded arithmetic is used in the physical step count. -/
def roundUpper (outer inner current width : Nat) : Nat :=
  outer*(3*inner*inner+inner*(2*current+4*width+33)+30)+
    (inner*inner+2)*outer*outer+8*inner+8*outer+26

theorem roundCost_le (outer inner current width : Nat) :
    roundCost outer inner current width ≤ roundUpper outer inner current width := by
  have h := Source284SquareLoopTotal.loopCost_formula outer inner 0 current width
  simp only [Nat.mul_zero,Nat.zero_add] at h
  unfold roundCost roundUpper
  nlinarith

theorem roundUpper_mono (outer inner width a b : Nat) (hab : a ≤ b) :
    roundUpper outer inner a width ≤ roundUpper outer inner b width := by
  unfold roundUpper
  gcongr

/-- The complete finite table has an explicit polynomial step bound for
every fixed number of passes, in both independent token lengths and the
initial counter and payload width. -/
theorem repeatCost_le (k outer inner current width : Nat) :
    repeatCost k outer inner current width ≤
      k*roundUpper outer inner (current+k*(outer*inner)) width := by
  induction k generalizing current with
  | zero => simp [repeatCost]
  | succ k ih =>
    simp only [repeatCost]
    have hround := roundCost_le outer inner current width
    have htail := ih (current+outer*inner)
    have he : current+outer*inner+k*(outer*inner)=current+(k+1)*(outer*inner) := by ring
    rw [he] at htail
    have hmono := roundUpper_mono outer inner width current (current+(k+1)*(outer*inner)) (by omega)
    calc
      roundCost outer inner current width + repeatCost k outer inner (current+outer*inner) width ≤
          roundUpper outer inner current width + k*roundUpper outer inner (current+(k+1)*(outer*inner)) width :=
        Nat.add_le_add hround htail
      _ ≤ roundUpper outer inner (current+(k+1)*(outer*inner)) width +
          k*roundUpper outer inner (current+(k+1)*(outer*inner)) width := Nat.add_le_add_right hmono _
      _ = (k+1)*roundUpper outer inner (current+(k+1)*(outer*inner)) width := by ring

end Shared.Beeping.NPcoNP.Source284RectangularRepeat
