import Shared.Beeping.NPcoNP.NativeHalfSelectorScan
import Shared.Beeping.NPcoNP.NativeHalfState97Progress

/-! A marker-conditional continuation of the physical state-97 scan through
the silent selector chain. The scanner preserves the encountered one to the
right, so the final state-92 rightward scan reaches it. This says nothing
about whether the actual machine reaches state 97 or has the marker. -/
namespace Shared.Beeping.NPcoNP.NativeHalfSelectorReturn

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.NativeHalfReturnFiniteSupport
open Shared.Beeping.NPcoNP.NativeHalfSelectorScan
open Shared.Beeping.NPcoNP.NativeHalfState97Progress

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- The state-97 scan leaves the one it found immediately right of its
state-83 head. -/
theorem scan97_marked (k : Nat) (h : Int) (t : Int → Bool)
    (hone : t (h-(k : Int)) = true) :
    ∃ n : Nat, 0 < n ∧ n ≤ k+1 ∧ t (h-(n : Int)+1) = true ∧
      silentSegment machine (cfg 97 h t) (cfg 83 (h-(n : Int)) t) n := by
  induction k generalizing h with
  | zero =>
    refine ⟨1, by omega, by omega, ?_, ?_⟩
    · simpa using hone
    · exact oneSeg machine _ _ (step97_one h t (by simpa using hone))
  | succ k ih =>
    cases hv : t h with
    | true =>
      refine ⟨1, by omega, by omega, ?_, ?_⟩
      · simpa using hv
      · exact oneSeg machine _ _ (step97_one h t hv)
    | false =>
      have he : (h-1)-(k : Int) = h-((Nat.succ k : Nat) : Int) := by push_cast; omega
      have hm : t ((h-1)-(k : Int)) = true := by rw [he]; exact hone
      obtain ⟨n, hn, hb, hmark, hs⟩ := ih (h-1) hm
      refine ⟨1+n, by omega, by omega, ?_, ?_⟩
      · have hp : (h-1)-(n : Int)+1 = h-((1+n : Nat) : Int)+1 := by push_cast; omega
        rw [← hp]; exact hmark
      · have hseg := segAdd machine _ _ _ 1 n (oneSeg machine _ _ (step97_zero h t hv)) hs
        have hp : (h-1)-(n : Int) = h-((1+n : Nat) : Int) := by push_cast; omega
        simpa [hp] using hseg

theorem row92_zero : machine.table.row 92 false = ⟨false,.right,92,false⟩ := by decide
theorem row92_one : machine.table.row 92 true = ⟨true,.right,93,false⟩ := by decide

theorem step92_zero (h : Int) (t : Int → Bool) (ht : t h = false) :
    machine.step (cfg 92 h t) = (cfg 92 (h+1) t,false) := by
  have hw : (⟨92,h,t⟩ : Config 284).write false = t := by
    rw [← ht]; exact write_current _
  simp [cfg, Machine.step, ht, row92_zero, Move.apply, hw]

theorem step92_one (h : Int) (t : Int → Bool) (ht : t h = true) :
    machine.step (cfg 92 h t) = (cfg 93 (h+1) t,false) := by
  have hw : (⟨92,h,t⟩ : Config 284).write true = t := by
    rw [← ht]; exact write_current _
  simp [cfg, Machine.step, ht, row92_one, Move.apply, hw]

theorem scan92_to_one (k : Nat) (h : Int) (t : Int → Bool)
    (hone : t (h+(k : Int)) = true) :
    ∃ n : Nat, 0 < n ∧ n ≤ k+1 ∧
      silentSegment machine (cfg 92 h t) (cfg 93 (h+(n : Int)) t) n := by
  induction k generalizing h with
  | zero =>
    refine ⟨1, by omega, by omega, ?_⟩
    exact oneSeg machine _ _ (step92_one h t (by simpa using hone))
  | succ k ih =>
    cases hv : t h with
    | true =>
      refine ⟨1, by omega, by omega, ?_⟩
      exact oneSeg machine _ _ (step92_one h t hv)
    | false =>
      have he : (h+1)+(k : Int) = h+((Nat.succ k : Nat) : Int) := by push_cast; omega
      have hm : t ((h+1)+(k : Int)) = true := by rw [he]; exact hone
      obtain ⟨n, hn, hb, hs⟩ := ih (h+1) hm
      refine ⟨1+n, by omega, by omega, ?_⟩
      have hseg := segAdd machine _ _ _ 1 n (oneSeg machine _ _ (step92_zero h t hv)) hs
      have hp : (h+1)+(n : Int) = h+((1+n : Nat) : Int) := by push_cast; omega
      simpa [hp] using hseg

/-- If the actual run visits state 97 with a one at or to the left of the
head, it reaches state 93 in positive finite silent time. The tape remains
unchanged. -/
theorem reachable_97_to_93 (time : Nat)
    (hstate : (machine.system.run time).state = 97)
    (p : Int) (hpos : p ≤ (machine.system.run time).head)
    (hone : (machine.system.run time).tape p = true) :
    ∃ (n : Nat) (e : Config 284), 0 < n ∧ e.state = 93 ∧
      e.tape = (machine.system.run time).tape ∧
      silentSegment machine (machine.system.run time) e n := by
  let c := machine.system.run time
  have hpos' : p ≤ c.head := hpos
  let k := (c.head-p).toNat
  have hp : c.head-(k : Int) = p := by
    have hn : 0 ≤ c.head-p := by omega
    have hk : (k : Int) = c.head-p := Int.toNat_of_nonneg hn
    omega
  have hone' : c.tape (c.head-(k : Int)) = true := by rw [hp]; exact hone
  obtain ⟨n, hn, _, hmark, hs⟩ := scan97_marked k c.head c.tape hone'
  obtain ⟨b, hb⟩ := run_has_left_zero time
  obtain ⟨m, hm, ht⟩ := chain_progress chain83 c.tape b hb (c.head-(n : Int))
  let h92 := c.head-(n : Int)-(m : Int)
  let k92 := ((c.head-(n : Int)+1)-h92).toNat
  have hk92 : h92+(k92 : Int) = c.head-(n : Int)+1 := by
    have hd : 0 ≤ (c.head-(n : Int)+1)-h92 := by dsimp [h92]; omega
    have he : (k92 : Int) = (c.head-(n : Int)+1)-h92 := Int.toNat_of_nonneg hd
    omega
  have hmark' : c.tape (h92+(k92 : Int)) = true := by rw [hk92]; exact hmark
  obtain ⟨l, hl, _, hu⟩ := scan92_to_one k92 h92 c.tape hmark'
  let e : Config 284 := cfg 93 (h92+(l : Int)) c.tape
  have hcfg : c = cfg 97 c.head c.tape := by
    have he : c = cfg c.state c.head c.tape := by cases c; rfl
    have hstate' : c.state = 97 := hstate
    simpa only [hstate'] using he
  refine ⟨(n+m)+l, e, by omega, rfl, rfl, ?_⟩
  change silentSegment machine c e (n+m+l)
  rw [hcfg]
  have hnt := segAdd machine _ _ _ n m hs ht
  exact segAdd machine _ _ _ (n+m) l hnt hu

end Shared.Beeping.NPcoNP.NativeHalfSelectorReturn
