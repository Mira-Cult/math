import Shared.Beeping.NPcoNP.Source284CounterOneSeed
import Shared.Beeping.NPcoNP.Source284ProductBlockPolynomial

/-! A fixed finite table seeds its own counter and builds a reusable product
block from two prepared blocks. The original blocks and payload are retained;
neither initial block is supplied by this module. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284SeededProductBlock

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284TokenCounterLoop (halves)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284CounterOneSeed.table (Source284ReusableProductBlock.table continuation)

def cost (outer inner width : Nat) : Nat :=
  Source284CounterOneSeed.cost width+Source284ReusableProductBlock.cost outer inner width

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (287+states) (table continuation) := by
  have hp := Source284ReusableProductBlock.closed states continuation hn hv
  have hs := Source284CounterOneSeed.closed (255+states)
    (Source284ReusableProductBlock.table continuation) (by omega) hp
  have he : 32+(255+states)=287+states := by omega
  rw [he] at hs
  exact hs

/-- The source table overwrites two high scratch bits to seed its counter,
then builds a new `outer*inner` token block and follows its continuation. -/
theorem product_then (outer inner : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate higher fuel : Nat) :
    run (table continuation)
      ⟨pairTape (List.replicate inner false) (pairTape (List.replicate outer false) certificate),
        2*flipped w higher,some 0⟩ (cost outer inner w.length+fuel) =
    shiftConfig 287 (run continuation
      ⟨pairTape (List.replicate (outer*inner) false)
          (pairTape (List.replicate inner false) (pairTape (List.replicate outer false) certificate)),
        2*flipped w (halves (2*(outer*inner)) ((higher/2)/2)),some 0⟩ fuel) := by
  have ht : cost outer inner w.length+fuel = Source284CounterOneSeed.cost w.length+
      (Source284ReusableProductBlock.cost outer inner w.length+fuel) := by simp [cost]; omega
  rw [ht]
  change run (Source284CounterOneSeed.table (Source284ReusableProductBlock.table continuation)) _ _ = _
  rw [Source284CounterOneSeed.seed_then,Source284ReusableProductBlock.product_then,
    Source284SourceRelocation.shiftConfig_add]

theorem encoded_product_then (outer inner states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate higher fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (encode (287+states) (table continuation) 1)
      ⟨pairTape (List.replicate inner false) (pairTape (List.replicate outer false) certificate),
        2*flipped w higher,active 0⟩ (cost outer inner w.length+fuel) =
    toSource (shiftConfig 287 (run continuation
      ⟨pairTape (List.replicate (outer*inner) false)
          (pairTape (List.replicate inner false) (pairTape (List.replicate outer false) certificate)),
        2*flipped w (halves (2*(outer*inner)) ((higher/2)/2)),some 0⟩ fuel)) := by
  let c : Config := ⟨pairTape (List.replicate inner false) (pairTape (List.replicate outer false) certificate),
    2*flipped w higher,some 0⟩
  have hc : Valid (287+states) c := by intro q hq; simp [c] at hq; omega
  have h := run_toSource (287+states) (table continuation) 1 c (closed states continuation hn hv) hc
    (cost outer inner w.length+fuel)
  rw [product_then] at h
  exact h

/-- In particular, a prepared `n^e` block and an `n` block produce a new
`n^(e+1)` block. The old blocks are retained behind the new one. -/
theorem power_block_then (e n : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate higher fuel : Nat) :
    run (table continuation)
      ⟨pairTape (List.replicate n false) (pairTape (List.replicate (n^e) false) certificate),
        2*flipped w higher,some 0⟩ (cost (n^e) n w.length+fuel) =
    shiftConfig 287 (run continuation
      ⟨pairTape (List.replicate (n^(e+1)) false)
          (pairTape (List.replicate n false) (pairTape (List.replicate (n^e) false) certificate)),
        2*flipped w (halves (2*(n^(e+1))) ((higher/2)/2)),some 0⟩ fuel) := by
  simpa [Nat.pow_succ] using product_then (n^e) n continuation w certificate higher fuel

noncomputable def costPolynomial (outer inner width : Polynomial Nat) : Polynomial Nat :=
  (4*width+14)+(4*width+16)+Source284ProductBlockPolynomial.costPolynomial outer inner width

theorem cost_polynomial (n o i w : Nat) (outer inner width : Polynomial Nat)
    (ho : o ≤ outer.eval n) (hi : i ≤ inner.eval n) (hw : w ≤ width.eval n) :
    cost o i w ≤ (costPolynomial outer inner width).eval n := by
  have hp := Source284ProductBlockPolynomial.cost_polynomial n o i w outer inner width ho hi hw
  unfold cost Source284CounterOneSeed.cost
  simp only [costPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
  omega

end Shared.Beeping.NPcoNP.Source284SeededProductBlock
