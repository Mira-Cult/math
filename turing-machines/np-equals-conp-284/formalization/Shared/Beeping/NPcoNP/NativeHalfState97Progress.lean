import Shared.Beeping.NPcoNP.NativeHalfState28Exit

/-! The literal state-97 leftward scanner. A leftward one forces its silent
exit to state 83; an all-zero left ray makes it scan silently forever. The
actual-run corollaries are conditional and establish no reachability or
global marker invariant. -/

namespace Shared.Beeping.NPcoNP.NativeHalfState97Progress

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfRows

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem row97_zero : machine.table.row 97 false = ⟨false, .left, 97, false⟩ := by decide
theorem row97_one : machine.table.row 97 true = ⟨true, .left, 83, false⟩ := by decide

theorem step97_zero (h : Int) (t : Int → Bool) (ht : t h = false) :
    machine.step (cfg 97 h t) = (cfg 97 (h-1) t, false) := by
  have hw : (⟨97,h,t⟩ : Config 284).write false = t := by
    rw [← ht]
    exact write_current _
  simp [cfg, Machine.step, ht, row97_zero, Move.apply, hw]

theorem step97_one (h : Int) (t : Int → Bool) (ht : t h = true) :
    machine.step (cfg 97 h t) = (cfg 83 (h-1) t, false) := by
  have hw : (⟨97,h,t⟩ : Config 284).write true = t := by
    rw [← ht]
    exact write_current _
  simp [cfg, Machine.step, ht, row97_one, Move.apply, hw]

/-- A one `k` cells to the left guarantees an exit no later than step `k+1`.
The entire tape is unchanged. -/
theorem scan_to_one (k : Nat) (h : Int) (t : Int → Bool)
    (hone : t (h-(k : Int)) = true) :
    ∃ (n : Nat), 0 < n ∧ n ≤ k+1 ∧
      silentSegment machine (cfg 97 h t) (cfg 83 (h-(n : Int)) t) n := by
  induction k generalizing h with
  | zero =>
    refine ⟨1, by omega, by omega, ?_⟩
    exact oneSeg machine _ _ (step97_one h t (by simpa using hone))
  | succ k ih =>
    cases hv : t h with
    | true =>
      refine ⟨1, by omega, by omega, ?_⟩
      exact oneSeg machine _ _ (step97_one h t hv)
    | false =>
      have he : (h-1)-(k : Int) = h-((Nat.succ k : Nat) : Int) := by push_cast; omega
      have hm : t ((h-1)-(k : Int)) = true := by rw [he]; exact hone
      obtain ⟨n, hn, hb, hs⟩ := ih (h-1) hm
      refine ⟨1+n, by omega, by omega, ?_⟩
      have hseg := segAdd machine _ _ _ 1 n (oneSeg machine _ _ (step97_zero h t hv)) hs
      have hp : (h-1)-(n : Int) = h-((1+n : Nat) : Int) := by push_cast; omega
      simpa [hp] using hseg

/-- If the actual run reaches 97 with a one at or to the left of its head,
the machine silently reaches state 83 in positive finite time. -/
theorem reachable_97_to_83 (time : Nat)
    (hstate : (machine.system.run time).state = 97)
    (p : Int) (hpos : p ≤ (machine.system.run time).head)
    (hone : (machine.system.run time).tape p = true) :
    ∃ (n : Nat) (e : Config 284), 0 < n ∧ e.state = 83 ∧
      silentSegment machine (machine.system.run time) e n := by
  let c := machine.system.run time
  have hpos' : p ≤ c.head := hpos
  let k := (c.head-p).toNat
  have hp : c.head - (k : Int) = p := by
    have hn : 0 ≤ c.head-p := by omega
    have hk : (k : Int) = c.head-p := Int.toNat_of_nonneg hn
    omega
  have hone' : c.tape (c.head-(k : Int)) = true := by rw [hp]; exact hone
  obtain ⟨n, hn, _, hs⟩ := scan_to_one k c.head c.tape hone'
  refine ⟨n, cfg 83 (c.head-(n : Int)) c.tape, hn, rfl, ?_⟩
  have hc : c = cfg 97 c.head c.tape := by
    have he : c = cfg c.state c.head c.tape := by cases c; rfl
    have hstate' : c.state = 97 := hstate
    simpa only [hstate'] using he
  simpa [← hc] using hs

/-- All-zero cells at and left of the head make every finite prefix a
silent state-97 scan, leaving the tape unchanged. -/
theorem scan_zeroes (h : Int) (t : Int → Bool)
    (hz : ∀ i : Nat, t (h-(i : Int)) = false) (n : Nat) :
    silentSegment machine (cfg 97 h t) (cfg 97 (h-(n : Int)) t) n := by
  induction n generalizing h with
  | zero => simp [silentSegment, W, WordEventSystem.advance, WordEventSystem.wordFrom]
  | succ n ih =>
    have h0 : t h = false := by simpa using hz 0
    have hz' : ∀ i : Nat, t ((h-1)-(i : Int)) = false := by
      intro i
      have he : (h-1)-(i : Int) = h-((i+1 : Nat) : Int) := by push_cast; omega
      rw [he]
      exact hz (i+1)
    have hs := segAdd machine _ _ _ 1 n (oneSeg machine _ _ (step97_zero h t h0))
      (ih (h-1) hz')
    have he : (h-1)-(n : Int) = h-((Nat.succ n : Nat) : Int) := by push_cast; omega
    simpa [he, Nat.add_comm] using hs

theorem zero_ray_silent (h : Int) (t : Int → Bool)
    (hz : ∀ i : Nat, t (h-(i : Int)) = false) (n : Nat) :
    (machine.system.advance (cfg 97 h t) n).state = 97 ∧
      ¬ machine.system.BeepFrom (cfg 97 h t) n := by
  have hs := scan_zeroes h t hz n
  have hs' := scan_zeroes h t hz (n+1)
  constructor
  · have ha := hs.1
    change (WordEventSystem.ofBeep machine.system).advance (cfg 97 h t) n =
      cfg 97 (h-(n : Int)) t at ha
    rw [ScalarWordRefinement.advance_ofBeep] at ha
    rw [ha]
    rfl
  · exact silent_no_beep machine _ _ _ n hs' (by omega)

/-- An adversarial finite-support configuration is not asserted reachable. -/
theorem blank_tape_trap (h : Int) :
    let t : Int → Bool := fun _ => false
    (∃ touched : List Int, ∀ p, p ∉ touched → t p = false) ∧
      ∀ n, (machine.system.advance (cfg 97 h t) n).state = 97 ∧
        ¬ machine.system.BeepFrom (cfg 97 h t) n := by
  dsimp only
  refine ⟨⟨[], by simp⟩, ?_⟩
  intro n
  exact zero_ray_silent h _ (by simp) n

end Shared.Beeping.NPcoNP.NativeHalfState97Progress
