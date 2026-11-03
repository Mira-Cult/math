import Shared.PNP.Record285.InitializationComposition

/-! Exact cellwise meaning of the candidate source-entry numeric configuration.
No theorem here asserts that the physical run reaches it. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 0
set_option exponentiation.threshold 8192
namespace Shared.PNP.Record285.InitializationEntryLayout
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.InitializationComposition
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.RelativeTape

/-- The base-four repunit has one bits at precisely its even positions. -/
theorem rep4_bit (n i : Nat) : (rep4 n).testBit i = true ↔ i % 2 = 0 ∧ i / 2 < n := by
  induction n generalizing i with
  | zero => simp [rep4]
  | succ n ih =>
    rw [rep4_succ]
    cases i with
    | zero => simp [Nat.testBit_zero]; omega
    | succ i =>
      cases i with
      | zero =>
        rw [Nat.testBit_add_one]
        simp [Nat.testBit_zero]
        omega
      | succ i =>
        rw [show i+1+1 = (i+1)+1 by omega, Nat.testBit_add_one, Nat.testBit_add_one]
        have he : (4*rep4 n+1)/2/2 = rep4 n := by omega
        rw [he, ih]
        constructor <;> intro h <;> omega

theorem candidate_right_bit (i : Nat) :
    (4^1910*rep4 1910).testBit i = true ↔ 3820 ≤ i ∧ i % 2 = 0 ∧ i < 7640 := by
  have hp : 4^1910 = 2^3820 := by decide
  rw [hp, Nat.testBit_two_pow_mul]
  simp only [Bool.and_eq_true, decide_eq_true_eq, rep4_bit]
  constructor <;> intro h <;> omega

theorem candidate_left_bit (i : Nat) :
    (6 : Nat).testBit i = true ↔ i = 1 ∨ i = 2 := by
  by_cases h : i < 3
  · have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl <;> decide
  · have hp : 2^3 ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    have hf : (6 : Nat).testBit i = false := Nat.testBit_lt_two_pow (by omega)
    simp [hf]
    omega

theorem candidate_control (physical : Shared.Beeping.Machines.Config 285)
    (h : Rel candidate physical) : physical.state.val = 284 ∧ physical.head = -3818 := by
  have hs : physical.state = ⟨284,by decide⟩ := h.1.symm
  exact ⟨by rw [hs], h.2.1.symm⟩

/-- The candidate relation specifies exactly the two left markers and the
alternating bank, with every other integer-indexed tape cell blank. -/
theorem candidate_tape (physical : Shared.Beeping.Machines.Config 285)
    (h : Rel candidate physical) (pos : Int) :
    physical.tape pos = true ↔
      pos = -3821 ∨ pos = -3820 ∨ (3 ≤ pos ∧ pos ≤ 3821 ∧ pos % 2 = 1) := by
  have hh : physical.head = -3818 := h.2.1.symm
  have ht := h.2.2
  have hhead : physical.tape (-3818) = false := by simpa [candidate,hh] using ht.1
  have hl (i : Nat) : physical.tape (-3818 - (i:Int) - 1) = (6:Nat).testBit i := by
    simpa [candidate,behindPos,hh] using ht.2.1 i
  have hr (i : Nat) : physical.tape (-3818 + (i:Int) + 1) = (4^1910*rep4 1910).testBit i := by
    simpa [candidate,aheadPos,hh] using ht.2.2 i
  have hc := positions_cover ⟨physical.tape,(-3818:Int),false⟩ pos
  simp only [behindPos,aheadPos,Bool.false_eq_true,if_false] at hc
  rcases hc with he | ⟨i,he⟩ | ⟨i,he⟩
  · subst pos
    simp [hhead]
  · subst pos
    rw [hl, candidate_left_bit]
    constructor <;> intro h <;> omega
  · subst pos
    rw [hr, candidate_right_bit]
    constructor <;> intro h <;> omega

/-- The root prefix is `110`, followed by the blank gap to the bank anchor. -/
theorem candidate_root_and_gap (physical : Shared.Beeping.Machines.Config 285)
    (h : Rel candidate physical) :
    physical.tape (-3821) = true ∧ physical.tape (-3820) = true ∧
      (∀ x, -3819 ≤ x → x ≤ 2 → physical.tape x = false) := by
  constructor
  · exact (candidate_tape physical h (-3821)).2 (by omega)
  constructor
  · exact (candidate_tape physical h (-3820)).2 (by omega)
  · intro x hlo hhi
    have hn : physical.tape x ≠ true := by
      intro hh
      have hc := (candidate_tape physical h x).1 hh
      omega
    cases hb : physical.tape x <;> simp_all

/-- One anchor pair and 1,909 further `10` pairs. Their count matches the
producer's fifteen active fields and 1,894 reserves; allocation is separate. -/
theorem candidate_zero_bank (physical : Shared.Beeping.Machines.Config 285)
    (h : Rel candidate physical) :
    physical.tape 3 = true ∧ physical.tape 4 = false ∧
      ∀ i : Nat, i < 1909 →
        physical.tape (5 + 2*(i:Int)) = true ∧ physical.tape (6 + 2*(i:Int)) = false := by
  have cell_one (x : Int) (hx : 3 ≤ x ∧ x ≤ 3821 ∧ x % 2 = 1) : physical.tape x = true :=
    (candidate_tape physical h x).2 (Or.inr (Or.inr hx))
  have cell_zero (x : Int) (hx : x ≠ -3821 ∧ x ≠ -3820 ∧
      ¬ (3 ≤ x ∧ x ≤ 3821 ∧ x % 2 = 1)) : physical.tape x = false := by
    have hn : physical.tape x ≠ true := by
      intro hh
      have hc := (candidate_tape physical h x).1 hh
      omega
    cases hb : physical.tape x <;> simp_all
  refine ⟨cell_one 3 (by decide), cell_zero 4 (by decide), ?_⟩
  intro i hi
  constructor
  · apply cell_one
    omega
  · apply cell_zero
    omega

end Shared.PNP.Record285.InitializationEntryLayout
