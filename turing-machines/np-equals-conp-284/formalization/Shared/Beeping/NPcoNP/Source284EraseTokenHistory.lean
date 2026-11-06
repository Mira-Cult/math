import Shared.Beeping.NPcoNP.Source284EraseZeroBlock
import Shared.Beeping.NPcoNP.Source284PolynomialRunwayRecovery

/-! Fixed unrolled finite tables remove every older token block after the
product stages. The exact original certificate is left on the tape, and the
cleared cells are moved past the protected input frame. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284EraseTokenHistory

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ProductIteration (historyAfter)

def table : Nat → (Nat → Bool → Row) → Nat → Bool → Row
  | 0, continuation => continuation
  | k+1, continuation => table k (Source284EraseZeroBlock.table continuation)

def cells : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | k+1, a, b => cells k b (a*b)+(2*a+2)

def cost : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _ => 0
  | k+1, a, b, width => cost k b (a*b) width+Source284EraseZeroBlock.cost (2*a) width

theorem closed (k states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) :
    Closed (30*k+states) (table k continuation) := by
  induction k generalizing states continuation with
  | zero => simpa [table] using hv
  | succ k ih =>
    have h := ih (30+states) (Source284EraseZeroBlock.table continuation)
      (by omega) (Source284EraseZeroBlock.closed states continuation hn hv)
    simpa [table,show 30*k+(30+states)=30*(k+1)+states by omega] using h

theorem block_form (n certificate : Nat) :
    pairTape (List.replicate n false) certificate = 2^(2*n+1)*(2*certificate+1) := by
  rw [Source284PolynomialRunwayRecovery.zerosBlock]
  have hp : 4^n = 2^(2*n) := by
    calc
      4^n = (2^2)^n := by norm_num
      _ = 2^(2*n) := by rw [pow_mul]
  rw [hp,pow_succ]
  ring

/-- The table removes exactly the finite stack described by `historyAfter`,
including all its marker bits; no mathematical decoder runs at runtime. -/
theorem erase_then (k a b : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate tail fuel : Nat) :
    run (table k continuation) ⟨historyAfter k a b certificate,2*flipped w tail,some 0⟩
      (cost k a b w.length+fuel) =
    shiftConfig (30*k) (run continuation
      ⟨certificate,2*flipped w (2^(cells k a b)*tail),some 0⟩ fuel) := by
  induction k generalizing a b continuation certificate tail fuel with
  | zero => simp [table,cost,cells,historyAfter,shiftConfig]
  | succ k ih =>
    have ht : cost (k+1) a b w.length+fuel =
        cost k b (a*b) w.length+(Source284EraseZeroBlock.cost (2*a) w.length+fuel) := by
      simp [cost]; omega
    rw [ht]
    change run (table k (Source284EraseZeroBlock.table continuation))
      ⟨historyAfter k b (a*b) (pairTape (List.replicate a false) certificate),
        2*flipped w tail,some 0⟩ _ = _
    rw [ih,block_form,Source284EraseZeroBlock.erase_then,
      Source284SourceRelocation.shiftConfig_add]
    simp only [cells]
    have hs : 30*k+30=30*(k+1) := by omega
    rw [hs]
    congr 2
    rw [pow_add]
    ring

noncomputable def costPolynomial : Nat → Polynomial Nat → Polynomial Nat → Polynomial Nat → Polynomial Nat
  | 0, _, _, _ => 0
  | k+1, a, b, width => costPolynomial k b (a*b) width +
      ((2*a+1)*(8*width+11)+(8*width+13))

/-- Exact polynomial for a fixed number of cleanup stages. -/
theorem costPolynomial_eval (k n : Nat) (a b width : Polynomial Nat) :
    (costPolynomial k a b width).eval n = cost k (a.eval n) (b.eval n) (width.eval n) := by
  induction k generalizing a b with
  | zero => simp [costPolynomial,cost]
  | succ k ih =>
    simp [costPolynomial,cost,Source284EraseZeroBlock.cost,ih,
      Polynomial.eval_add,Polynomial.eval_mul]

end Shared.Beeping.NPcoNP.Source284EraseTokenHistory
