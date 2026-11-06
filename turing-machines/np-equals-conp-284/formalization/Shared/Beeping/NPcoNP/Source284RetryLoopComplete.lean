import Shared.Beeping.NPcoNP.Source284RetryLoop

/-! Repeat the fixed retry table on prepared tapes and bound the complete
comparison-and-growth run by a cubic polynomial in payload length. -/
set_option maxRecDepth 2048
namespace Shared.Beeping.NPcoNP.Source284RetryLoopComplete

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284PayloadMarkOne (zeros)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284RetryLoop (table)

theorem retry_all (continuation : Nat → Bool → Row) (k : Nat) (w : List Bool)
    (certificate tail : Nat) (hlt : k < w.length) :
    run (table continuation) ⟨pairTape (List.replicate k false) certificate,
      2*flipped (w++[false]) tail,some 0⟩ (Source284OneRetry.cost k w.length) =
    ⟨pairTape (List.replicate (k+1) false) certificate,2*flipped (w++[false]) (tail/4),some 0⟩ := by
  have hdlen : 0 < (w.drop k).length := by simp; omega
  cases hd : w.drop k with
  | nil => simp [hd] at hdlen
  | cons b rest =>
    have hw : w = w.take k ++ b::rest := by
      have h := List.take_append_drop k w
      rw [hd] at h
      exact h.symm
    have hlen : (w.take k).length = k := by
      simp [List.length_take,Nat.min_eq_left (by omega : k ≤ w.length)]
    have hp := Source284RetryLoop.retry continuation (w.take k) rest b certificate tail
    rw [hlen,← hw] at hp
    exact hp

def retriesCost (k n : Nat) : Nat → Nat
  | 0 => 0
  | count+1 => Source284OneRetry.cost k n + retriesCost (k+1) n count

/-- The iteration count is used only to state the time and prove the
invariant; the finite table restarts itself after each actual retry. -/
theorem retries (continuation : Nat → Bool → Row) (count k : Nat) (w : List Bool)
    (certificate tail : Nat) (hbound : k+count ≤ w.length) :
    run (table continuation) ⟨pairTape (List.replicate k false) certificate,
      2*flipped (w++[false]) tail,some 0⟩ (retriesCost k w.length count) =
    ⟨pairTape (List.replicate (k+count) false) certificate,
      2*flipped (w++[false]) (tail/4^count),some 0⟩ := by
  induction count generalizing k tail with
  | zero => simp [retriesCost,run]
  | succ count ih =>
    have hk : k < w.length := by omega
    have hi : k+1+count ≤ w.length := by omega
    simp only [retriesCost]
    rw [run_add,retry_all continuation k w certificate tail hk,ih (k+1) (tail/4) hi]
    have hd : (tail/4)/4^count = tail/4^(count+1) := by
      rw [Nat.div_div_eq_div_mul,pow_succ]
      congr 1
      ring
    have hk' : k+1+count = k+(count+1) := by omega
    rw [hd,hk']

def totalCost (k n : Nat) : Nat := retriesCost k n (n-k)+(4*n*n+20*n+17)

/-- From any all-zero prepared token count at most the payload length, the
fixed table autonomously grows to equality and enters the caller. The final
step's head position and the consumed high suffix are explicit. -/
theorem complete (continuation : Nat → Bool → Row) (k : Nat) (w : List Bool)
    (certificate tail : Nat) (hle : k ≤ w.length) :
    run (table continuation) ⟨pairTape (List.replicate k false) certificate,
      2*flipped (w++[false]) tail,some 0⟩ (totalCost k w.length) =
    ⟨2*pairTape (List.replicate w.length true) certificate,
      zeros w (flipped [false] (tail/4^(w.length-k))),some 98⟩ := by
  unfold totalCost
  rw [run_add,retries continuation (w.length-k) k w certificate tail (by omega)]
  have hk : k+(w.length-k) = w.length := by omega
  rw [hk,Source284RetryLoop.finish_equal]

theorem retryCost_le (k n : Nat) (hk : k ≤ n) :
    Source284OneRetry.cost k n ≤ 4*n*n+36*n+56 := by
  rw [Source284OneRetry.cost_formula]
  have hs : k*k ≤ n*n := Nat.mul_self_le_mul_self hk
  nlinarith

theorem retriesCost_le (count k n : Nat) (hbound : k+count ≤ n) :
    retriesCost k n count ≤ count*(4*n*n+36*n+56) := by
  induction count generalizing k with
  | zero => simp [retriesCost]
  | succ count ih =>
    have hk : k ≤ n := by omega
    have hi : k+1+count ≤ n := by omega
    have h1 := retryCost_le k n hk
    have h2 := ih (k+1) hi
    simp only [retriesCost]
    calc
      Source284OneRetry.cost k n + retriesCost (k+1) n count ≤
          (4*n*n+36*n+56)+count*(4*n*n+36*n+56) := Nat.add_le_add h1 h2
      _ = (count+1)*(4*n*n+36*n+56) := by ring

/-- A bit-step bound in payload length; no cost depends on a hidden high
suffix counter or on a unit-cost unbounded integer. -/
theorem totalCost_le (k n : Nat) (hle : k ≤ n) :
    totalCost k n ≤ 4*n*n*n+40*n*n+76*n+17 := by
  have h := retriesCost_le (n-k) k n (by omega)
  have hm : (n-k)*(4*n*n+36*n+56) ≤ n*(4*n*n+36*n+56) := by
    exact Nat.mul_le_mul_right _ (Nat.sub_le n k)
  unfold totalCost
  have hr : n*(4*n*n+36*n+56)+(4*n*n+20*n+17) = 4*n*n*n+40*n*n+76*n+17 := by ring
  omega

end Shared.Beeping.NPcoNP.Source284RetryLoopComplete
