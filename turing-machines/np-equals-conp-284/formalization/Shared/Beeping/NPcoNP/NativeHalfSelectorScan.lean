import Shared.Beeping.NPcoNP.NativeHalfReturnFiniteSupport

/-! Finite, silent, tape-preserving progress of the literal table's 14
leftward selector scans. Every scan advances after finding a zero; a left-zero
tail therefore guarantees the whole chain reaches state 92. The actual-run
corollary uses blank-start finite support and does not assert reachability of
state 83 or progress after state 92. -/
namespace Shared.Beeping.NPcoNP.NativeHalfSelectorScan

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfReturnFiniteSupport
open Shared.Beeping.NPcoNP.NativeHalfRows

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

inductive ScanRow : Fin 284 → Fin 284 → Prop where
  | r83 : ScanRow 83 82 | r82 : ScanRow 82 81 | r81 : ScanRow 81 80
  | r80 : ScanRow 80 91 | r91 : ScanRow 91 90 | r90 : ScanRow 90 89
  | r89 : ScanRow 89 88 | r88 : ScanRow 88 87 | r87 : ScanRow 87 86
  | r86 : ScanRow 86 85 | r85 : ScanRow 85 84 | r84 : ScanRow 84 79
  | r79 : ScanRow 79 78 | r78 : ScanRow 78 92

theorem row_zero {q r : Fin 284} (hr : ScanRow q r) :
    machine.table.row q false = ⟨false,.left,r,false⟩ := by
  cases hr <;> decide

theorem row_one {q r : Fin 284} (hr : ScanRow q r) :
    machine.table.row q true = ⟨true,.left,q,false⟩ := by
  cases hr <;> decide

theorem step_zero {q r : Fin 284} (hr : ScanRow q r) (h : Int)
    (t : Int → Bool) (ht : t h = false) :
    machine.step (cfg q h t) = (cfg r (h-1) t,false) := by
  have hw : (⟨q,h,t⟩ : Config 284).write false = t := by
    rw [← ht]
    exact write_current _
  simp [cfg, Machine.step, ht, row_zero hr, Move.apply, hw]

theorem step_one {q r : Fin 284} (hr : ScanRow q r) (h : Int)
    (t : Int → Bool) (ht : t h = true) :
    machine.step (cfg q h t) = (cfg q (h-1) t,false) := by
  have hw : (⟨q,h,t⟩ : Config 284).write true = t := by
    rw [← ht]
    exact write_current _
  simp [cfg, Machine.step, ht, row_one hr, Move.apply, hw]

/-- One selector scan exits within `k+1` steps if the cell at distance `k`
is zero. Its head moves left once per step and its tape is unchanged. -/
theorem scan {q r : Fin 284} (hr : ScanRow q r) (k : Nat) (h : Int)
    (t : Int → Bool) (hz : t (h-(k : Int)) = false) :
    ∃ n : Nat, 0 < n ∧ n ≤ k+1 ∧
      silentSegment machine (cfg q h t) (cfg r (h-(n : Int)) t) n := by
  induction k generalizing h with
  | zero =>
    refine ⟨1, by omega, by omega, ?_⟩
    exact oneSeg machine _ _ (step_zero hr h t (by simpa using hz))
  | succ k ih =>
    cases hv : t h with
    | false =>
      refine ⟨1, by omega, by omega, ?_⟩
      exact oneSeg machine _ _ (step_zero hr h t hv)
    | true =>
      have he : (h-1)-(k : Int) = h-((Nat.succ k : Nat) : Int) := by push_cast; omega
      have hz' : t ((h-1)-(k : Int)) = false := by rw [he]; exact hz
      obtain ⟨n, hn, hb, hs⟩ := ih (h-1) hz'
      refine ⟨1+n, by omega, by omega, ?_⟩
      have hs' := segAdd machine _ _ _ 1 n (oneSeg machine _ _ (step_one hr h t hv)) hs
      have he' : (h-1)-(n : Int) = h-((1+n : Nat) : Int) := by push_cast; omega
      simpa [he'] using hs'

inductive Chain : Nat → Fin 284 → Fin 284 → Prop where
  | refl (q) : Chain 0 q q
  | cons {m q r s} : ScanRow q r → Chain m r s → Chain (m+1) q s

theorem chain83 : Chain 14 83 92 := by
  apply Chain.cons ScanRow.r83
  apply Chain.cons ScanRow.r82
  apply Chain.cons ScanRow.r81
  apply Chain.cons ScanRow.r80
  apply Chain.cons ScanRow.r91
  apply Chain.cons ScanRow.r90
  apply Chain.cons ScanRow.r89
  apply Chain.cons ScanRow.r88
  apply Chain.cons ScanRow.r87
  apply Chain.cons ScanRow.r86
  apply Chain.cons ScanRow.r85
  apply Chain.cons ScanRow.r84
  apply Chain.cons ScanRow.r79
  apply Chain.cons ScanRow.r78
  exact Chain.refl 92

/-- A zero tail suffices for any finite chain of these scans. -/
theorem chain_progress {m : Nat} {q r : Fin 284} (hc : Chain m q r)
    (t : Int → Bool) (b : Int) (hz : ∀ p ≤ b, t p = false) (h : Int) :
    ∃ n : Nat, m ≤ n ∧
      silentSegment machine (cfg q h t) (cfg r (h-(n : Int)) t) n := by
  induction hc generalizing h with
  | refl q =>
    refine ⟨0, by omega, ?_⟩
    simp [silentSegment, W, WordEventSystem.advance, WordEventSystem.wordFrom]
  | @cons m q r s hr rest ih =>
    let k := (h - min b h).toNat
    have hk : h - (k : Int) ≤ b := by
      have hn : 0 ≤ h - min b h := by omega
      have he : (k : Int) = h - min b h := Int.toNat_of_nonneg hn
      omega
    obtain ⟨n, hn, _, hs⟩ := scan hr k h t (hz _ hk)
    obtain ⟨l, hl, hs'⟩ := ih (h-(n : Int))
    refine ⟨n+l, by omega, ?_⟩
    have hseg := segAdd machine _ _ _ n l hs hs'
    have he : h-(n : Int)-(l : Int) = h-((n+l : Nat) : Int) := by push_cast; omega
    simpa [he] using hseg

/-- Every actual state-83 visit reaches state 92 after at least 14 silent
transitions, with unchanged tape. -/
theorem reachable_83_to_92 (time : Nat)
    (hstate : (machine.system.run time).state = 83) :
    ∃ n : Nat, 14 ≤ n ∧
      silentSegment machine (machine.system.run time)
        (cfg 92 ((machine.system.run time).head-(n : Int)) (machine.system.run time).tape) n := by
  obtain ⟨b, hb⟩ := run_has_left_zero time
  let c := machine.system.run time
  obtain ⟨n, hn, hs⟩ := chain_progress chain83 c.tape b hb c.head
  refine ⟨n, hn, ?_⟩
  have hcfg : c = cfg 83 c.head c.tape := by
    have he : c = cfg c.state c.head c.tape := by cases c; rfl
    have hcstate : c.state = 83 := hstate
    simpa only [hcstate] using he
  simpa [← hcfg] using hs

end Shared.Beeping.NPcoNP.NativeHalfSelectorScan
