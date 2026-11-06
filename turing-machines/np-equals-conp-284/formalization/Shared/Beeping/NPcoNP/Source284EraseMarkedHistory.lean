import Shared.Beeping.NPcoNP.Source284EraseMarkedBlock
import Shared.Beeping.NPcoNP.Source284EraseTokenHistory

/-! The paid cleanup of a complete nested block history, recording every
cleared cell in a scratch counter instead of discarding the workspace size. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284EraseMarkedHistory

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ProductIteration (historyAfter)
open Shared.Beeping.NPcoNP.Source284ScratchMarkedLoop (marks)
open Shared.Beeping.NPcoNP.Source284EraseTokenHistory (cells cost)

def table : Nat → (Nat → Bool → Row) → Nat → Bool → Row
  | 0, continuation => continuation
  | k+1, continuation => table k (Source284EraseMarkedBlock.table continuation)

theorem closed (k states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) :
    Closed (30*k+states) (table k continuation) := by
  induction k generalizing states continuation with
  | zero => simpa [table] using hv
  | succ k ih =>
    have h := ih (30+states) (Source284EraseMarkedBlock.table continuation)
      (by omega) (Source284EraseMarkedBlock.closed states continuation hn hv)
    simpa [table,show 30*k+(30+states)=30*(k+1)+states by omega] using h

theorem marks_add (m n tail : Nat) : marks m (marks n tail) = marks (m+n) tail := by
  induction m with
  | zero => simp [marks]
  | succ m ih =>
    rw [Source284EraseMarkedBlock.marks_succ,ih]
    have h : m+1+n = (m+n)+1 := by omega
    rw [h,Source284EraseMarkedBlock.marks_succ]

theorem erase_then (k a b : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate tail fuel : Nat) :
    run (table k continuation) ⟨historyAfter k a b certificate,2*flipped w tail,some 0⟩
      (cost k a b w.length+fuel) =
    shiftConfig (30*k) (run continuation
      ⟨certificate,2*flipped w (marks (cells k a b) tail),some 0⟩ fuel) := by
  induction k generalizing a b continuation certificate tail fuel with
  | zero => simp [table,cost,cells,historyAfter,shiftConfig,marks]
  | succ k ih =>
    have ht : cost (k+1) a b w.length+fuel =
        cost k b (a*b) w.length+(Source284EraseZeroBlock.cost (2*a) w.length+fuel) := by
      simp [cost]; omega
    rw [ht]
    change run (table k (Source284EraseMarkedBlock.table continuation))
      ⟨historyAfter k b (a*b) (pairTape (List.replicate a false) certificate),
        2*flipped w tail,some 0⟩ _ = _
    rw [ih,Source284EraseTokenHistory.block_form,Source284EraseMarkedBlock.erase_then,
      Source284SourceRelocation.shiftConfig_add]
    simp only [cells]
    have hs : 30*k+30=30*(k+1) := by omega
    rw [hs]
    congr 2
    simp [marks_add,Nat.add_comm]

noncomputable def cellsPolynomial : Nat → Polynomial Nat → Polynomial Nat → Polynomial Nat
  | 0, _, _ => 0
  | k+1, a, b => cellsPolynomial k b (a*b)+(2*a+2)

theorem cellsPolynomial_eval (k n : Nat) (a b : Polynomial Nat) :
    (cellsPolynomial k a b).eval n = cells k (a.eval n) (b.eval n) := by
  induction k generalizing a b with
  | zero => simp [cellsPolynomial,cells]
  | succ k ih => simp [cellsPolynomial,cells,ih,Polynomial.eval_add,Polynomial.eval_mul]

end Shared.Beeping.NPcoNP.Source284EraseMarkedHistory
