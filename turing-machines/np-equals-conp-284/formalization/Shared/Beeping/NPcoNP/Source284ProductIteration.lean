import Shared.Beeping.NPcoNP.Source284SeededProductBlock

/-! A fixed number of paid product-and-recycle stages. Each new block is
pushed in front of the previous two; their lengths evolve by `(a,b) ↦
(b,a*b)`. The complete older block stack and high suffix are preserved. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284ProductIteration

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284TokenCounterLoop (halves)

def table : Nat → (Nat → Bool → Row) → Nat → Bool → Row
  | 0, continuation => continuation
  | k+1, continuation => Source284SeededProductBlock.table (table k continuation)

def outerAfter : Nat → Nat → Nat → Nat
  | 0, a, _ => a
  | k+1, a, b => outerAfter k b (a*b)

def innerAfter : Nat → Nat → Nat → Nat
  | 0, _, b => b
  | k+1, a, b => innerAfter k b (a*b)

def historyAfter : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, certificate => certificate
  | k+1, a, b, certificate => historyAfter k b (a*b) (pairTape (List.replicate a false) certificate)

def suffixAfter : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, higher => higher
  | k+1, a, b, higher => suffixAfter k b (a*b) (halves (2*(a*b)) ((higher/2)/2))

def cost : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _ => 0
  | k+1, a, b, width => Source284SeededProductBlock.cost a b width + cost k b (a*b) width

theorem closed (k states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (287*k+states) (table k continuation) := by
  induction k with
  | zero => simpa [table] using hv
  | succ k ih =>
    have hs := Source284SeededProductBlock.closed (287*k+states) (table k continuation) (by omega) ih
    have he : 287+(287*k+states)=287*(k+1)+states := by omega
    rw [he] at hs
    exact hs

/-- All stages run in one fixed finite table, with every counter seed,
product, recycling pass and continuation offset charged. -/
theorem iterate_then (k a b : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate higher fuel : Nat) :
    run (table k continuation)
      ⟨pairTape (List.replicate b false) (pairTape (List.replicate a false) certificate),
        2*flipped w higher,some 0⟩ (cost k a b w.length+fuel) =
    shiftConfig (287*k) (run continuation
      ⟨pairTape (List.replicate (innerAfter k a b) false)
          (pairTape (List.replicate (outerAfter k a b) false) (historyAfter k a b certificate)),
        2*flipped w (suffixAfter k a b higher),some 0⟩ fuel) := by
  induction k generalizing a b certificate higher with
  | zero => simp [table,cost,innerAfter,outerAfter,historyAfter,suffixAfter,shiftConfig]
  | succ k ih =>
    have ht : cost (k+1) a b w.length+fuel = Source284SeededProductBlock.cost a b w.length+
        (cost k b (a*b) w.length+fuel) := by simp [cost]; omega
    rw [ht]
    change run (Source284SeededProductBlock.table (table k continuation)) _ _ = _
    rw [Source284SeededProductBlock.product_then,ih,Source284SourceRelocation.shiftConfig_add]
    simp only [innerAfter,outerAfter,historyAfter,suffixAfter]
    have he : 287+287*k=287*(k+1) := by omega
    rw [he]

noncomputable def costPolynomial : Nat → Polynomial Nat → Polynomial Nat → Polynomial Nat → Polynomial Nat
  | 0, _, _, _ => 0
  | k+1, a, b, width => Source284SeededProductBlock.costPolynomial a b width+
      costPolynomial k b (a*b) width

/-- For fixed `k`, polynomial bounds on the two initial block sizes and
payload width yield one explicit polynomial transition bound for all stages. -/
theorem cost_polynomial (k n a b width : Nat) (A B W : Polynomial Nat)
    (ha : a ≤ A.eval n) (hb : b ≤ B.eval n) (hw : width ≤ W.eval n) :
    cost k a b width ≤ (costPolynomial k A B W).eval n := by
  induction k generalizing a b A B with
  | zero => simp [cost,costPolynomial]
  | succ k ih =>
    simp only [cost,costPolynomial,Polynomial.eval_add]
    have hp := Source284SeededProductBlock.cost_polynomial n a b width A B W ha hb hw
    have hab : a*b ≤ (A*B).eval n := by
      rw [Polynomial.eval_mul]
      exact Nat.mul_le_mul ha hb
    have ht := ih b (a*b) B (A*B) hb hab
    omega

end Shared.Beeping.NPcoNP.Source284ProductIteration
