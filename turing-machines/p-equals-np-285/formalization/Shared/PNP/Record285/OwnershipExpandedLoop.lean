import Shared.PNP.Record285.OwnershipExpandedCheck
import Shared.PNP.Record285.OwnershipMoveLoop

/-! Exact full-bank semantics for a primitive implementation of an atomic
ownership move, for arbitrary natural-valued stores. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.OwnershipCore
open Shared.Beeping

def expandedCycle (src dst : Nat) (bank : Nat → Nat) : Nat → Nat :=
  update (.inc dst) (update (.dec src) bank)

theorem expandedCycle_read (src dst j : Nat) (bank : Nat → Nat) (hne : src ≠ dst) :
    expandedCycle src dst bank j =
      if j = src then bank src - 1 else if j = dst then bank dst + 1 else bank j := by
  by_cases hs : j = src
  · subst j
    simp [expandedCycle,update,hne]
  · by_cases hd : j = dst
    · subst j
      simp [expandedCycle,update,Ne.symm hne]
    · simp [expandedCycle,update,hs,hd]

theorem zero_move_identity (src dst : Nat) (bank : Nat → Nat) (hz : bank src = 0) :
    update (.move src dst) bank = bank := by
  funext j
  by_cases hs : j = src
  · subst j
    simp [update,hz]
  · by_cases hd : j = dst
    · subst j
      simp [update,hs,hz]
    · simp [update,hs,hd]

theorem zero_decrement_identity (src : Nat) (bank : Nat → Nat) (hz : bank src = 0) :
    update (.dec src) bank = bank := by
  funext j
  by_cases hs : j = src
  · subst j
    simp [update,hz]
  · simp [update,hs]

theorem cycle_move_identity (src dst : Nat) (bank : Nat → Nat) (hne : src ≠ dst)
    (hpos : 0 < bank src) :
    update (.move src dst) (expandedCycle src dst bank) = update (.move src dst) bank := by
  funext j
  by_cases hs : j = src
  · subst j
    simp [update]
  · by_cases hd : j = dst
    · subst j
      have hsrc := expandedCycle_read src dst src bank hne
      have hdst := expandedCycle_read src dst dst bank hne
      simp only [if_true] at hsrc
      simp only [if_neg (Ne.symm hne),if_true] at hdst
      simp only [update,if_neg (Ne.symm hne),if_true]
      rw [hsrc,hdst]
      omega
    · have h := expandedCycle_read src dst j bank hne
      simp only [if_neg hs,if_neg hd] at h
      simp only [update,if_neg hs,if_neg hd]
      exact h

theorem expandedCycle_run (rows : Array Row) (head body exit src dst : Nat) (bank : Nat → Nat)
    (hhead : rows[head]? = some ⟨.dec src,body,exit⟩)
    (hbody : rows[body]? = some ⟨.inc dst,head,head⟩) (hpos : 0 < bank src) :
    (system rows).advance ⟨head,bank⟩ 2 = ⟨head,expandedCycle src dst bank⟩ ∧
      ∀ j, j < 2 → ¬ (system rows).BeepFrom ⟨head,bank⟩ j := by
  have hfirst : step rows ⟨head,bank⟩ = (⟨body,update (.dec src) bank⟩,false) := by
    have hn : bank src ≠ 0 := by omega
    simp [step,hhead,observe,hn]
  have hsecond : step rows ⟨body,update (.dec src) bank⟩ =
      (⟨head,expandedCycle src dst bank⟩,false) := by
    simp [step,hbody,observe,expandedCycle]
  constructor
  · change (step rows (step rows ⟨head,bank⟩).1).1 = _
    rw [hfirst,hsecond]
  · intro j hj
    have hc : j = 0 ∨ j = 1 := by omega
    rcases hc with rfl | rfl
    · change ¬ (step rows ⟨head,bank⟩).2 = true
      rw [hfirst]
      simp
    · change ¬ (step rows (step rows ⟨head,bank⟩).1).2 = true
      rw [hfirst,hsecond]
      simp

/-- Every move loop terminates in `2*n+1` transitions, exactly implements the
atomic whole-bank update, and emits no event. -/
theorem expanded_move_run (rows : Array Row) (head body exit src dst n : Nat) (bank : Nat → Nat)
    (hhead : rows[head]? = some ⟨.dec src,body,exit⟩)
    (hbody : rows[body]? = some ⟨.inc dst,head,head⟩)
    (hne : src ≠ dst) (hvalue : bank src = n) :
    (system rows).advance ⟨head,bank⟩ (2*n+1) = ⟨exit,update (.move src dst) bank⟩ ∧
      ∀ t, t < 2*n+1 → ¬ (system rows).BeepFrom ⟨head,bank⟩ t := by
  induction n generalizing bank with
  | zero =>
    have hid := zero_move_identity src dst bank hvalue
    have hdec := zero_decrement_identity src bank hvalue
    have hfirst : step rows ⟨head,bank⟩ = (⟨exit,bank⟩,false) := by
      simp [step,hhead,observe,hvalue,hdec]
    constructor
    · change (step rows ⟨head,bank⟩).1 = ⟨exit,update (.move src dst) bank⟩
      rw [hfirst,hid]
    · intro t ht
      have ht0 : t = 0 := by omega
      subst t
      change ¬ (step rows ⟨head,bank⟩).2 = true
      rw [hfirst]
      simp
  | succ n ih =>
    have hpos : 0 < bank src := by omega
    have hcycle := expandedCycle_run rows head body exit src dst bank hhead hbody hpos
    let mid := expandedCycle src dst bank
    have hmid : mid src = n := by
      have h := expandedCycle_read src dst src bank hne
      simp only [if_true] at h
      change expandedCycle src dst bank src = n
      omega
    obtain ⟨hrun,hquiet⟩ := ih mid hmid
    have htime : 2*(n+1)+1 = 2+(2*n+1) := by omega
    constructor
    · rw [htime,advance_add,hcycle.1]
      rw [cycle_move_identity src dst bank hne hpos] at hrun
      exact hrun
    · intro t ht he
      by_cases hsmall : t < 2
      · exact hcycle.2 t hsmall he
      · have ht' : t-2 < 2*n+1 := by omega
        apply hquiet (t-2) ht'
        unfold EventSystem.BeepFrom at he ⊢
        have htEq : t = 2+(t-2) := by omega
        rw [htEq,advance_add,hcycle.1] at he
        exact he

end Shared.PNP.Record285.OwnershipCore
