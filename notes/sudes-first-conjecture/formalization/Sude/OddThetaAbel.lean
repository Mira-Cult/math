import Sude.PoolPartialSummation
import Sude.BMORFinite

/-! Exact discrete Abel summation for the odd-prime theta function.
No prime-distribution estimate or integral identity is assumed here. -/
namespace Sude
noncomputable section
open scoped BigOperators

/-- At a natural endpoint, the modulus-two progression is exactly the
closed odd-prime prefix, with the prime 2 excluded. -/
theorem apPrefix_two_one_nat (X : ℕ) :
    apPrefix (X : ℝ) 2 1 = oddPrimePrefix X := by
  ext p
  have hx : 0 ≤ (X : ℝ) := Nat.cast_nonneg X
  rw [mem_apPrefix_iff _ _ _ hx]
  simp only [oddPrimePrefix, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  change (Nat.Prime p ∧ (p : ℝ) ≤ (X : ℝ) ∧ (p : ℤ) % 2 = 1) ↔
    (p ≤ X ∧ Nat.Prime p ∧ p ≠ 2)
  have hm : ((p : ℤ) % 2 = 1) ↔ p % 2 = 1 := by exact_mod_cast Iff.rfl
  rw [hm]
  have hcast : ((p : ℝ) ≤ X) ↔ p ≤ X := by exact_mod_cast Iff.rfl
  rw [hcast]
  constructor
  · rintro ⟨hp, hle, hodd⟩
    refine ⟨hle, hp, ?_⟩
    intro heq
    subst p
    norm_num at hodd
  · rintro ⟨hle, hp, hne⟩
    exact ⟨hp, hle, hp.eq_two_or_odd.resolve_left hne⟩

/-- Exact finite Abel summation: the count and theta prefix both include the
upper endpoint. The terms at 0 and 1 use the totalized real inverse. -/
theorem oddPrimePrefix_theta_abel (X : ℕ) :
    ((oddPrimePrefix X).card : ℝ) +
      ∑ k ∈ Finset.range X, thetaAP (k : ℝ) 2 1 *
        ((Real.log (k + 1 : ℕ))⁻¹ - (Real.log (k : ℝ))⁻¹) =
      thetaAP (X : ℝ) 2 1 * (Real.log (X : ℝ))⁻¹ := by
  classical
  let S := oddPrimePrefix X
  let g : ℕ → ℝ := fun p => if p ∈ S then Real.log p else 0
  let w : ℕ → ℝ := fun p => (Real.log p)⁻¹
  have hsub : S ⊆ Finset.range (X + 1) := by
    intro p hp
    simp only [S, oddPrimePrefix, Finset.mem_filter] at hp
    exact hp.1
  have hweighted : (∑ p ∈ Finset.range (X + 1), w p * g p) = (S.card : ℝ) := by
    rw [← Finset.sum_subset hsub]
    · calc
        (∑ p ∈ S, w p * g p) = ∑ _p ∈ S, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro p hp
          have hpprime : Nat.Prime p := (Finset.mem_filter.mp hp).2.1
          have hp2 : (1 : ℝ) < p := by exact_mod_cast hpprime.one_lt
          have hl : Real.log (p : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hp2)
          simp [w, g, hp, hl]
        _ = (S.card : ℝ) := by simp
    · intro p hp hnot
      simp [g, hnot]
  have hpartial (k : ℕ) (hk : k ≤ X) :
      (∑ p ∈ Finset.range (k + 1), g p) = thetaAP (k : ℝ) 2 1 := by
    rw [thetaAP_eq_sum_apPrefix, apPrefix_two_one_nat]
    have hset : (Finset.range (k + 1)).filter (fun p => p ∈ S) = oddPrimePrefix k := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, S, oddPrimePrefix]
      constructor
      · rintro ⟨hpk, _, hp, hne⟩
        exact ⟨hpk, hp, hne⟩
      · rintro ⟨hpk, hp, hne⟩
        exact ⟨hpk, le_trans hpk hk, hp, hne⟩
    simp only [g, ← Finset.sum_filter]
    rw [hset]
  have hab := Finset.sum_range_by_parts w g (X + 1)
  simp only [smul_eq_mul, Nat.add_sub_cancel] at hab
  rw [hweighted, hpartial X le_rfl] at hab
  have hsum : (∑ k ∈ Finset.range X, (w (k + 1) - w k) *
        (∑ p ∈ Finset.range (k + 1), g p)) =
      ∑ k ∈ Finset.range X, thetaAP (k : ℝ) 2 1 * (w (k + 1) - w k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hpartial k (Finset.mem_range.mp hk).le]
    ring
  rw [hsum] at hab
  dsimp [w] at hab
  linarith

end
end Sude
