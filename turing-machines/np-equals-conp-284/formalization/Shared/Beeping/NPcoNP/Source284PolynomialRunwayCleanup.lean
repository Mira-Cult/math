import Shared.Beeping.NPcoNP.Source284PositivePolynomialTwoSided
import Shared.Beeping.NPcoNP.Source284EraseTokenHistory

/-! Paid cleanup following the polynomial workspace construction. It removes
all temporary token blocks and restores the arbitrary certificate, moving
the cleared cells across the protected frame. The left-side runway must be
rebuilt before the guarded verifier can use this layout. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284PolynomialRunwayCleanup

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ProductIteration (outerAfter historyAfter)
open Shared.Beeping.NPcoNP.Source284PositivePolynomialRunway (block)

def zeros (k n : Nat) : Nat :=
  2*(block k n+1)+2*outerAfter k (n+2) (n+2)

def table (k : Nat) (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284EraseZeroBlock.table (Source284EraseTokenHistory.table k continuation)

def description (k states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284PositivePolynomialTwoSided.description k (30+30*k+states) (table k continuation)

def cleanupCost (k : Nat) (w : List Bool) : Nat :=
  Source284EraseZeroBlock.cost (zeros k w.length) (w++[false]).length+
    Source284EraseTokenHistory.cost k (w.length+2) (w.length+2) (w++[false]).length

def totalCost (k : Nat) (w : List Bool) : Nat :=
  Source284PositivePolynomialTwoSided.totalCost k w+cleanupCost k w

def finalTail (k n suffix : Nat) : Nat :=
  2^(Source284EraseTokenHistory.cells k (n+2) (n+2))*
    (2^(zeros k n+2)*(2^(block k n+1)*Source284PositivePolynomialTwoSided.retained k n suffix))

theorem closed (k states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) :
    Closed (30+30*k+states) (table k continuation) := by
  have hh := Source284EraseTokenHistory.closed k states continuation hn hv
  have hz := Source284EraseZeroBlock.closed (30*k+states)
    (Source284EraseTokenHistory.table k continuation) (by omega) hh
  simpa [table,show 30+(30*k+states)=30+30*k+states by omega] using hz

theorem top_form (m outer history : Nat) :
    4^(m+1)*pairTape (List.replicate outer false) history =
      2^(2*(m+1)+2*outer+1)*(2*history+1) := by
  rw [Source284EraseTokenHistory.block_form]
  have hp : 4^(m+1) = 2^(2*(m+1)) := by
    calc
      4^(m+1) = (2^2)^(m+1) := by norm_num
      _ = 2^(2*(m+1)) := by rw [pow_mul]
  rw [hp,← Nat.mul_assoc,← pow_add]
  congr 1

/-- The original certificate is physically restored after a positive finite
source run. The entire existing left gap and token stack are transferred to
the other side; this result does not assert a remaining left-hand gap. -/
theorem source_then (k states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix fuel : Nat) (hn : 0 < states)
    (hv : Closed states continuation) :
    Source284Relative.run (description k states continuation)
      (Source284Relative.initial (Source284Parser.encodeFrame w suffix) certificate)
      (totalCost k w+fuel) =
    toSource (shiftConfig (664+317*k) (run continuation
      ⟨certificate,2*flipped (w++[false]) (finalTail k w.length suffix),some 0⟩ fuel)) := by
  have hc := closed k states continuation hn hv
  have h := Source284PositivePolynomialTwoSided.source_then k (30+30*k+states)
    (table k continuation) w certificate suffix (cleanupCost k w+fuel) (by omega) hc
  have ht : totalCost k w+fuel = Source284PositivePolynomialTwoSided.totalCost k w+
      (cleanupCost k w+fuel) := by simp [totalCost]; omega
  rw [ht]
  change Source284Relative.run (Source284PositivePolynomialTwoSided.description k
    (30+30*k+states) (table k continuation)) _ _ = _
  rw [h]
  simp only [cleanupCost,table]
  rw [top_form]
  change toSource (shiftConfig (634+287*k)
    (run (Source284EraseZeroBlock.table (Source284EraseTokenHistory.table k continuation))
      ⟨2^(zeros k w.length+1)*
        (2*historyAfter k (w.length+2) (w.length+2) certificate+1),_,some 0⟩ _)) = _
  rw [show Source284EraseZeroBlock.cost (zeros k w.length) (w++[false]).length+
      Source284EraseTokenHistory.cost k (w.length+2) (w.length+2) (w++[false]).length+fuel =
      Source284EraseZeroBlock.cost (zeros k w.length) (w++[false]).length+
        (Source284EraseTokenHistory.cost k (w.length+2) (w.length+2) (w++[false]).length+fuel) by omega]
  rw [Source284EraseZeroBlock.erase_then,Source284EraseTokenHistory.erase_then]
  repeat rw [Source284SourceRelocation.shiftConfig_add]
  have hs : 634+287*k+30+30*k=664+317*k := by omega
  rw [hs]
  rfl

noncomputable def zerosPolynomial (k : Nat) : Polynomial Nat :=
  2*(Source284PositivePolynomialRunway.blockPolynomial k+1)+
    2*Source284ProductIterationPolynomial.outerPolynomial k (Polynomial.X+2) (Polynomial.X+2)

noncomputable def cleanupPolynomial (k : Nat) : Polynomial Nat :=
  (zerosPolynomial k+1)*(8*(Polynomial.X+1)+11)+(8*(Polynomial.X+1)+13)+
    Source284EraseTokenHistory.costPolynomial k (Polynomial.X+2) (Polynomial.X+2) (Polynomial.X+1)

noncomputable def costPolynomial (k : Nat) : Polynomial Nat :=
  Source284PositivePolynomialTwoSided.costPolynomial k+cleanupPolynomial k

theorem cleanupPolynomial_eval (k : Nat) (w : List Bool) :
    (cleanupPolynomial k).eval w.length = cleanupCost k w := by
  simp [cleanupPolynomial,cleanupCost,zerosPolynomial,zeros,Source284EraseZeroBlock.cost,
    Source284PositivePolynomialRunway.blockPolynomial_eval,
    Source284ProductIterationPolynomial.outer_eval,
    Source284EraseTokenHistory.costPolynomial_eval,Polynomial.eval_add,Polynomial.eval_mul]

/-- The complete paid preparation and block cleanup use a fixed polynomial
number of source transitions for every framed input and certificate. -/
theorem totalCost_polynomial (k : Nat) (w : List Bool) :
    totalCost k w ≤ (costPolynomial k).eval w.length := by
  have h := Source284PositivePolynomialTwoSided.totalCost_polynomial k w
  simp only [costPolynomial,Polynomial.eval_add,cleanupPolynomial_eval]
  simp only [totalCost]
  omega

end Shared.Beeping.NPcoNP.Source284PolynomialRunwayCleanup
