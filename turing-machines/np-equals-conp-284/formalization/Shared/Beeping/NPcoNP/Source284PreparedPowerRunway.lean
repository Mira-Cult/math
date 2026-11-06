import Shared.Beeping.NPcoNP.Source284PreparedPowerStage
import Shared.Beeping.NPcoNP.Source284CountedShift

/-! A paid finite continuation turns a prepared power-product counter into
an actual one-sided zero runway. Preparation of the token blocks, a second
runway, recycling, and the physical beeper binding are separate obligations. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284PreparedPowerRunway

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284CountedShift (counter)
open Shared.Beeping.NPcoNP.Source284TokenCounterLoop (halves)
open Shared.Beeping.NPcoNP.Source284RectangularRepeat (repeatCost)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284SquareRepeat.repeatTable 1 (Source284CountedShift.table continuation)

def elapsed (e n width : Nat) : Nat :=
  repeatCost 1 n (n^e) 0 width+(n^(e+1)+1)*(4*width+7)

theorem elapsed_positive (e n width : Nat) : 0 < elapsed e n width := by
  have hp : 0 < (n^(e+1)+1)*(4*width+7) := Nat.mul_pos (by omega) (by omega)
  unfold elapsed
  omega

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (131+states) (table continuation) := by
  have hc := Source284CountedShift.closed states continuation hn hv
  have hs := Source284SquareRepeat.repeat_closed 1 (21+states)
    (Source284CountedShift.table continuation) (by omega) hc
  have he : 110*1+(21+states)=131+states := by omega
  rw [he] at hs
  exact hs

/-- The same finite table performs the product stage and then consumes the
counter to create `n^(e+1)+1` zero cells on the opposite tape half. Both
prepared blocks and the certificate remain beyond those zeros. -/
theorem runway_then (e n : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate higher fuel : Nat) :
    run (table continuation)
      ⟨pairTape (List.replicate (n^e) false) (pairTape (List.replicate n false) certificate),
        2*flipped w (counter 0 higher),some 0⟩ (elapsed e n w.length+fuel) =
    shiftConfig 131 (run continuation
      ⟨2^(n^(e+1)+1)*
        pairTape (List.replicate (n^e) false) (pairTape (List.replicate n false) certificate),
        2*flipped w (halves (n^(e+1)) higher),some 0⟩ fuel) := by
  have ht : elapsed e n w.length+fuel = repeatCost 1 n (n^e) 0 w.length+
      ((n^(e+1)+1)*(4*w.length+7)+fuel) := by simp [elapsed]; omega
  rw [ht]
  change run (Source284SquareRepeat.repeatTable 1 (Source284CountedShift.table continuation)) _ _ = _
  rw [Source284PreparedPowerStage.power_stage,Source284CountedShift.countdown_after]
  simp only [Source284SourceRelocation.shiftConfig_add]

/-- The encoded source machine implements the prepared-table run exactly,
including every shifted transition and the preserved higher suffix. -/
theorem encoded_runway_then (e n states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate higher fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (encode (131+states) (table continuation) 1)
      ⟨pairTape (List.replicate (n^e) false) (pairTape (List.replicate n false) certificate),
        2*flipped w (counter 0 higher),active 0⟩ (elapsed e n w.length+fuel) =
    toSource (shiftConfig 131 (run continuation
      ⟨2^(n^(e+1)+1)*
        pairTape (List.replicate (n^e) false) (pairTape (List.replicate n false) certificate),
        2*flipped w (halves (n^(e+1)) higher),some 0⟩ fuel)) := by
  let c : Config := ⟨pairTape (List.replicate (n^e) false) (pairTape (List.replicate n false) certificate),
    2*flipped w (counter 0 higher),some 0⟩
  have hc : Valid (131+states) c := by intro q hq; simp [c] at hq; omega
  have h := run_toSource (131+states) (table continuation) 1 c (closed states continuation hn hv) hc
    (elapsed e n w.length+fuel)
  rw [runway_then] at h
  exact h

/-- At the paid handoff, the actual encoded source tape has the promised
finite zero prefix, regardless of the high certificate and scratch suffix. -/
theorem encoded_zero_runway (e n states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate higher : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ left right,
      Source284Relative.run (encode (131+states) (table continuation) 1)
        ⟨pairTape (List.replicate (n^e) false) (pairTape (List.replicate n false) certificate),
          2*flipped w (counter 0 higher),active 0⟩ (elapsed e n w.length) =
        ⟨left,right,active 131⟩ ∧ 2^(n^(e+1)+1) ∣ left := by
  let suffix := pairTape (List.replicate (n^e) false) (pairTape (List.replicate n false) certificate)
  refine ⟨2^(n^(e+1)+1)*suffix,2*flipped w (halves (n^(e+1)) higher),?_,?_⟩
  · have h := encoded_runway_then e n states continuation w certificate higher 0 hn hv
    simpa [suffix,run,shiftConfig,toSource,nextState] using h
  · exact ⟨suffix,rfl⟩

noncomputable def costPolynomial (e : Nat) : Polynomial Nat :=
  Source284RectangularPolynomial.costPolynomial 1 Polynomial.X (Polynomial.X^e) 0 (Polynomial.X+1) +
    (Polynomial.X^(e+1)+1)*(4*(Polynomial.X+1)+7)

/-- For fixed `e`, all product and zero-insertion steps have a polynomial
bound when the preserved payload width is at most `n+1`. -/
theorem elapsed_polynomial (e n width : Nat) (hwidth : width ≤ n+1) :
    elapsed e n width ≤ (costPolynomial e).eval n := by
  have hp := Source284PreparedPowerStage.powerCost_polynomial e n width hwidth
  have hs : (n^(e+1)+1)*(4*width+7) ≤ (n^(e+1)+1)*(4*(n+1)+7) := by gcongr
  unfold elapsed
  rw [show (costPolynomial e).eval n =
      (Source284RectangularPolynomial.costPolynomial 1 Polynomial.X (Polynomial.X^e) 0 (Polynomial.X+1)).eval n+
        (n^(e+1)+1)*(4*(n+1)+7) by
        simp [costPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X]]
  omega

end Shared.Beeping.NPcoNP.Source284PreparedPowerRunway
