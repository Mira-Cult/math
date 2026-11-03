import Shared.PNP.Record285.OwnershipClassSum

/-! Exact, terminating physical core implementation of an ownership move.
The retained bank suffix is arbitrary; the whole output bank is explicitly
the iterated decrement/increment transformation. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.OwnershipCore
open Shared.Beeping
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarExact
open Shared.PNP.Record285.GrammarCoreGraph
open Shared.PNP.Record285.GrammarCoreZero

def moveCycle (src dst : Nat) (fields : List Nat) : List Nat :=
  applyUpdate (.inc dst) (applyUpdate (.dec src) fields)

def moveBank (src dst : Nat) : Nat → List Nat → List Nat
  | 0, fields => fields
  | n+1, fields => moveBank src dst n (moveCycle src dst fields)

theorem advance_add {α : Type} (M : EventSystem α) (s : α) (n k : Nat) :
    M.advance s (n+k) = M.advance (M.advance s n) k := by
  induction k with
  | zero => simp [EventSystem.advance]
  | succ k ih =>
    change (M.step (M.advance s (n+k))).1 = _
    rw [ih]
    rfl

theorem test_dec (fields : List Nat) (src : Nat) :
    GrammarControlGraph.test (.dec src) fields = decide (fields.getD src 0 = 0) := by
  simp [GrammarControlGraph.test]

theorem cycle_length (fields : List Nat) (src dst : Nat) (hlen : 15 ≤ fields.length)
    (hs : src < 15) (hd : dst < 15) : fields.length ≤ (moveCycle src dst fields).length := by
  have h1 : fields.length ≤ (applyUpdate (.dec src) fields).length :=
    bank_length_nondecreasing (.dec src) fields (by intro i hi; simp [operationIndex] at hi; omega)
  have h2 : (applyUpdate (.dec src) fields).length ≤ (moveCycle src dst fields).length :=
    bank_length_nondecreasing (.inc dst) _ (by intro i hi; simp [operationIndex] at hi; omega)
  omega

theorem cycle_read (fields : List Nat) (src dst j : Nat) (hlen : 15 ≤ fields.length)
    (hs : src < 15) (hd : dst < 15) (hne : src ≠ dst) (hj : j < 15) :
    (moveCycle src dst fields).getD j 0 =
      if j = src then fields.getD src 0 - 1 else
      if j = dst then fields.getD dst 0 + 1 else fields.getD j 0 := by
  let mid := applyUpdate (.dec src) fields
  have hlen' : 15 ≤ mid.length := by
    have h := bank_length_nondecreasing (.dec src) fields
      (by intro i hi; simp [operationIndex] at hi; omega)
    dsimp [mid]
    omega
  have hread1 (i : Nat) (hi : i < 15) : mid.getD i 0 =
      if i = src then fields.getD src 0 - 1 else fields.getD i 0 := by
    have h := bank_update_correct (.dec src) fields
      (by intro i hi; simp [operationIndex] at hi; omega) i (by omega)
    simpa [updateBank,operationIndex,operationValue,mid] using h
  have hread2 := bank_update_correct (.inc dst) mid
    (by intro i hi; simp [operationIndex] at hi; omega) j (by omega)
  change (applyUpdate (.inc dst) mid).getD j 0 = _
  rw [hread2]
  simp only [updateBank,operationIndex,operationValue]
  by_cases hjs : j = src
  · subst j
    simp only [if_neg hne]
    simpa only [if_pos rfl] using hread1 src hs
  · by_cases hjd : j = dst
    · subst j
      simp only [if_neg (Ne.symm hne)]
      have h := hread1 dst hd
      simp only [if_neg (Ne.symm hne)] at h
      rw [h]
    · simp only [if_neg hjs,if_neg hjd]
      have h := hread1 j hj
      simp only [if_neg hjs] at h
      exact h

/-- One positive source unit takes exactly a decrement and an increment,
returns to the test, and emits no event. -/
theorem cycle_run (rows : Array CoreRow) (head body exit src dst : Nat) (fields : List Nat)
    (hhead : rows[head]? = some ⟨.dec src,body,exit⟩)
    (hbody : rows[body]? = some ⟨.inc dst,head,head⟩)
    (hpos : 0 < fields.getD src 0) :
    (coreSystem rows).advance ⟨head,fields⟩ 2 = ⟨head,moveCycle src dst fields⟩ ∧
      ∀ j, j < 2 → ¬ (coreSystem rows).BeepFrom ⟨head,fields⟩ j := by
  have htest : GrammarControlGraph.test (.dec src) fields = false := by
    rw [test_dec]
    exact decide_eq_false (by omega)
  have hfirst : coreStep rows ⟨head,fields⟩ =
      (⟨body,applyUpdate (.dec src) fields⟩,false) := by
    simp only [coreStep,hhead,Option.getD_some,htest]
    rfl
  have hsecond : coreStep rows ⟨body,applyUpdate (.dec src) fields⟩ =
      (⟨head,moveCycle src dst fields⟩,false) := by
    simp [coreStep,hbody,GrammarControlGraph.test,moveCycle]
  constructor
  · change (coreStep rows (coreStep rows ⟨head,fields⟩).1).1 = _
    rw [hfirst,hsecond]
  · intro j hj
    have hc : j = 0 ∨ j = 1 := by omega
    rcases hc with rfl | rfl
    · change ¬ (coreStep rows ⟨head,fields⟩).2 = true
      rw [hfirst]
      simp
    · change ¬ (coreStep rows (coreStep rows ⟨head,fields⟩).1).2 = true
      rw [hfirst,hsecond]
      simp

/-- The complete ownership loop terminates after exactly `2*n+1` core
transitions, preserves an arbitrary bank frame, and emits no events. -/
theorem move_loop (rows : Array CoreRow) (head body exit src dst n : Nat) (fields : List Nat)
    (hhead : rows[head]? = some ⟨.dec src,body,exit⟩)
    (hbody : rows[body]? = some ⟨.inc dst,head,head⟩)
    (hlen : 15 ≤ fields.length) (hs : src < 15) (hd : dst < 15) (hne : src ≠ dst)
    (hvalue : fields.getD src 0 = n) :
    (coreSystem rows).advance ⟨head,fields⟩ (2*n+1) = ⟨exit,moveBank src dst n fields⟩ ∧
    15 ≤ (moveBank src dst n fields).length ∧
    (∀ j, j < 15 → (moveBank src dst n fields).getD j 0 =
      if j = src then 0 else if j = dst then fields.getD dst 0 + n else fields.getD j 0) ∧
    ∀ t, t < 2*n+1 → ¬ (coreSystem rows).BeepFrom ⟨head,fields⟩ t := by
  induction n generalizing fields with
  | zero =>
    have hz : (fields.drop src).headD 0 = 0 := by rw [drop_head_getD,hvalue]
    have hid := decrement_zero_identity fields src (by omega) hz
    have htest : GrammarControlGraph.test (.dec src) fields = true := by
      rw [test_dec,hvalue]
      decide
    have hfirst : coreStep rows ⟨head,fields⟩ = (⟨exit,fields⟩,false) := by
      simp only [coreStep,hhead,Option.getD_some,htest,if_true,hid]
      rfl
    refine ⟨?_,?_,?_,?_⟩
    · change (coreStep rows ⟨head,fields⟩).1 = ⟨exit,fields⟩
      rw [hfirst]
    · exact hlen
    · intro j hj
      change fields.getD j 0 =
        if j = src then 0 else if j = dst then fields.getD dst 0 + 0 else fields.getD j 0
      by_cases hjs : j = src
      · subst j
        simp only [if_true]
        exact hvalue
      · by_cases hjd : j = dst
        · subst j
          simp only [if_neg (Ne.symm hne),if_true,Nat.add_zero]
        · simp only [if_neg hjs,if_neg hjd]
    · intro t ht
      have ht0 : t = 0 := by omega
      subst t
      change ¬ (coreStep rows ⟨head,fields⟩).2 = true
      rw [hfirst]
      simp
  | succ n ih =>
    have hpos : 0 < fields.getD src 0 := by omega
    have hcycle := cycle_run rows head body exit src dst fields hhead hbody hpos
    let mid := moveCycle src dst fields
    have hmidlen : 15 ≤ mid.length := by
      have h := cycle_length fields src dst hlen hs hd
      change 15 ≤ (moveCycle src dst fields).length
      omega
    have hmidvalue : mid.getD src 0 = n := by
      have h := cycle_read fields src dst src hlen hs hd hne hs
      simp only [if_true] at h
      change (moveCycle src dst fields).getD src 0 = n
      omega
    obtain ⟨hadvance,hfinalLength,hreads,hquiet⟩ := ih mid hmidlen hmidvalue
    have htime : 2*(n+1)+1 = 2+(2*n+1) := by omega
    refine ⟨?_,?_,?_,?_⟩
    · rw [htime,advance_add,hcycle.1]
      exact hadvance
    · exact hfinalLength
    · intro j hj
      have hr := hreads j hj
      have hc := cycle_read fields src dst j hlen hs hd hne hj
      change (moveBank src dst n mid).getD j 0 = _
      by_cases hjs : j = src
      · subst j
        simpa using hr
      · by_cases hjd : j = dst
        · subst j
          change mid.getD dst 0 = _ at hc
          simp only [if_neg (Ne.symm hne),if_true] at hr hc ⊢
          omega
        · simp only [if_neg hjs,if_neg hjd] at hr hc ⊢
          exact hr.trans hc
    · intro t ht hbeep
      by_cases hsmall : t < 2
      · exact hcycle.2 t hsmall hbeep
      · have ht' : t-2 < 2*n+1 := by omega
        apply hquiet (t-2) ht'
        unfold EventSystem.BeepFrom at hbeep ⊢
        have htEq : t = 2+(t-2) := by omega
        rw [htEq,advance_add,hcycle.1] at hbeep
        exact hbeep

end Shared.PNP.Record285.OwnershipCore
