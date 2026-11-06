import Shared.Beeping.NPcoNP.Source284DoubleTokenErase
import Shared.Beeping.NPcoNP.Source284RawSquareRepeat
import Shared.Beeping.NPcoNP.Source284ScratchCounterClear

/-! Fixed-coefficient quadratic input-side clearing from a flipped frame. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284FlippedScaledQuadratic

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284TokenCounterLoop (halves)
open Shared.Beeping.NPcoNP.Source284LengthGrowLoop (totalTime quarters)
open Shared.Beeping.NPcoNP.Source284LengthGrowSource (setupCost)
open Shared.Beeping.NPcoNP.Source284SquareRepeat (repeatTable repeatCost)

def table (k : Nat) (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284LengthGrowRawContinue.setup
    (Source284LengthGrowRawContinue.setup
      (Source284FlippedCounterSeed.table
        (repeatTable k (Source284DoubleTokenErase.table
          (Source284ScratchCounterClear.table continuation)))))

def nextTail (n tail : Nat) : Nat := quarters n ((quarters n ((tail/2)/2)/2)/2)

def cost (k : Nat) (w : List Bool) : Nat :=
  2*(setupCost w+totalTime [] w)+(4*(w++[false]).length+14)+
    repeatCost k w.length 0 (w++[false]).length +
    (8*w.length+4*w.length+18)+(4*(w++[false]).length+2*(k*(w.length*w.length))+14)

theorem closed (k states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (354+110*k+states) (table k continuation) := by
  have h1 := Source284ScratchCounterClear.closed states continuation hn hv
  have h2 := Source284DoubleTokenErase.closed (15+states) (Source284ScratchCounterClear.table continuation) (by omega) h1
  have h3 := Source284SquareRepeat.repeat_closed k (29+(15+states))
    (Source284DoubleTokenErase.table (Source284ScratchCounterClear.table continuation)) (by omega) h2
  have h4 := Source284FlippedCounterSeed.closed (110*k+(29+(15+states)))
    (repeatTable k (Source284DoubleTokenErase.table (Source284ScratchCounterClear.table continuation))) (by omega) h3
  have h5 := Source284LengthGrowRawContinue.setup_closed (16+(110*k+(29+(15+states))))
    (Source284FlippedCounterSeed.table (repeatTable k (Source284DoubleTokenErase.table (Source284ScratchCounterClear.table continuation)))) (by omega) h4
  have h6 := Source284LengthGrowRawContinue.setup_closed (147+(16+(110*k+(29+(15+states)))))
    (Source284LengthGrowRawContinue.setup (Source284FlippedCounterSeed.table
      (repeatTable k (Source284DoubleTokenErase.table (Source284ScratchCounterClear.table continuation))))) (by omega) h5
  have he : 147+(147+(16+(110*k+(29+(15+states)))))=354+110*k+states := by omega
  rw [he] at h6
  exact h6

/-- Both temporary token blocks are erased before the fixed-coefficient
input suffix is cleared, preserving the old certificate-side tape. -/
theorem prepare_then (k : Nat) (continuation : Nat → Bool → Row) (w : List Bool) (certificate tail fuel : Nat) :
    run (table k continuation) ⟨certificate,2*flipped (w++[false]) tail,some 0⟩ (cost k w+fuel) =
    shiftConfig (354+110*k) (run continuation
      ⟨4^(w.length+1)*(4^(w.length+1)*certificate),
        2*flipped (w++[false]) (2^(k*(w.length*w.length)+1)*halves (k*(w.length*w.length)) (nextTail w.length tail/2)),some 0⟩ fuel) := by
  have ht : cost k w+fuel = setupCost w+(totalTime [] w+
      (setupCost w+(totalTime [] w+((4*(w++[false]).length+14)+
      (repeatCost k w.length 0 (w++[false]).length+
      ((8*w.length+4*w.length+18)+((4*(w++[false]).length+2*(k*(w.length*w.length))+14)+fuel))))))) := by
    simp [cost]; omega
  rw [ht]
  unfold table
  rw [Source284LengthGrowRawContinue.setup_then,Source284LengthGrowRawContinue.setup_then,
    Source284FlippedCounterSeed.seed_then]
  have hl := Source284SquareRepeat.repeat_then k
    (Source284DoubleTokenErase.table (Source284ScratchCounterClear.table continuation))
    w.length 0 (w++[false]) certificate (nextTail w.length tail/2)
    ((8*w.length+4*w.length+18)+((4*(w++[false]).length+2*(k*(w.length*w.length))+14)+fuel))
  simp only [Nat.zero_add] at hl
  rw [show quarters w.length ((quarters w.length ((tail/2)/2)/2)/2) = nextTail w.length tail by rfl]
  rw [hl]
  have he := Source284DoubleTokenErase.erase_then (Source284ScratchCounterClear.table continuation)
    w.length (List.replicate w.length false) certificate
    (flipped (w++[false]) (Source284CountedShift.counter (k*(w.length*w.length))
      (halves (k*(w.length*w.length)) (nextTail w.length tail/2))))
    ((4*(w++[false]).length+2*(k*(w.length*w.length))+14)+fuel)
  simp only [List.length_replicate] at he
  rw [he,Source284ScratchCounterClear.clear_scratch_then]
  repeat rw [Source284SourceRelocation.shiftConfig_add]
  have hs : 147+147+16+110*k+29+15=354+110*k := by omega
  rw [hs]

end Shared.Beeping.NPcoNP.Source284FlippedScaledQuadratic
