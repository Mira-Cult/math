import Shared.Beeping.NPcoNP.Source284RawCounterShift
import Shared.Beeping.NPcoNP.Source284FlippedCounterSeed
import Shared.Beeping.NPcoNP.Source284TokenCounterContinue

/-! A prepared token block drives a paid finite table that creates a
one-sided zero runway. The initial scratch suffix is arbitrary. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284PreparedTokenRunway

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284TokenCounterLoop (halves consumeTime)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284FlippedCounterSeed.table (Source284TokenCounterLoop.table (Source284RawCounterShift.adapter continuation))

def cost (m width : Nat) : Nat :=
  (4*width+14)+consumeTime m 0 0 width+2+(m+1)*(4*width+7)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (71+states) (table continuation) := by
  have ha := Source284RawCounterShift.adapter_closed states continuation hn hv
  have ht := Source284TokenCounterLoop.closed (23+states) (Source284RawCounterShift.adapter continuation) (by omega) ha
  have hs := Source284FlippedCounterSeed.closed (32+(23+states))
    (Source284TokenCounterLoop.table (Source284RawCounterShift.adapter continuation)) (by omega) ht
  have he : 16+(32+(23+states))=71+states := by omega
  rw [he] at hs
  exact hs

/-- The table seeds a counter, counts every token, pays the exhaustion
handoff and inserts `m+1` zeros without reading arbitrary high suffix data. -/
theorem runway_then (m : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate higher fuel : Nat) :
    run (table continuation) ⟨pairTape (List.replicate m false) certificate,2*flipped w higher,some 0⟩
      (cost m w.length+fuel) =
    shiftConfig 71 (run continuation
      ⟨2^(m+1)*pairTape (List.replicate m true) certificate,
        2*flipped w (halves m (higher/2)),some 0⟩ fuel) := by
  have ht : cost m w.length+fuel = (4*w.length+14)+
      (consumeTime m 0 0 w.length+(2+((m+1)*(4*w.length+7)+fuel))) := by simp [cost]; omega
  rw [ht]
  unfold table
  rw [Source284FlippedCounterSeed.seed_then,Source284ScratchScanner.run_add]
  have hc := Source284TokenCounterLoop.consume (Source284RawCounterShift.adapter continuation)
    m 0 w 0 certificate (higher/2)
  simp only [List.replicate_zero,List.nil_append,Nat.zero_add] at hc
  rw [hc]
  change shiftConfig 16 (run (Source284TokenCounterLoop.table (Source284RawCounterShift.adapter continuation))
    (shiftConfig 32 ⟨pairTape (List.replicate m true) certificate,
      2*flipped w (Source284CountedShift.counter m (halves m (higher/2))),some 1⟩) _) = _
  rw [Source284TokenCounterContinue.relocated_run,Source284ScratchScanner.run_add,Source284RawCounterShift.enter]
  change shiftConfig 16 (shiftConfig 32 (run (Source284RawCounterShift.adapter continuation)
    (shiftConfig 2 ⟨pairTape (List.replicate m true) certificate,
      2*flipped w (Source284CountedShift.counter m (halves m (higher/2))),some 0⟩) _)) = _
  rw [Source284RawCounterShift.relocated_run,Source284CountedShift.countdown_after]
  simp only [Source284SourceRelocation.shiftConfig_add]

noncomputable def costPolynomial (block width : Polynomial Nat) : Polynomial Nat :=
  (4*width+14)+(3*block*block+block*(4*width+25)+8)+2+(block+1)*(4*width+7)

theorem cost_polynomial (n m width : Nat) (block w : Polynomial Nat)
    (hm : m ≤ block.eval n) (hw : width ≤ w.eval n) :
    cost m width ≤ (costPolynomial block w).eval n := by
  rw [show (costPolynomial block w).eval n =
    (4*w.eval n+14)+(3*(block.eval n)*(block.eval n)+block.eval n*(4*w.eval n+25)+8)+2+
      (block.eval n+1)*(4*w.eval n+7) by
      simp [costPolynomial,Polynomial.eval_add,Polynomial.eval_mul]]
  unfold cost
  rw [Source284TokenCounterLoop.consumeTime_formula]
  simp only [Nat.mul_zero,Nat.zero_add]
  have hquad : 3*m*m ≤ 3*(block.eval n)*(block.eval n) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 3 hm) hm
  have hlinear : m*(4*width+25) ≤ block.eval n*(4*w.eval n+25) :=
    Nat.mul_le_mul hm (by omega)
  have hlast : (m+1)*(4*width+7) ≤ (block.eval n+1)*(4*w.eval n+7) :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

end Shared.Beeping.NPcoNP.Source284PreparedTokenRunway
