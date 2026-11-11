import Sude.PrimePrefixSpec
import Mathlib.Algebra.BigOperators.Module

/-! Exact finite partial summation for the prescribed odd-prime pool.
This module uses no analytic estimate for prime counts or mean values. -/
namespace Sude
noncomputable section
open scoped BigOperators

/-- Finite Abel summation for an arbitrary real weight on a bounded finite
set of natural numbers. The counting function includes its upper endpoint. -/
theorem finite_count_partial_summation (S : Finset ℕ) (X : ℕ) (w : ℕ → ℝ)
    (hbound : ∀ p ∈ S, p ≤ X) :
    (∑ p ∈ S, w p) +
      ∑ k ∈ Finset.range X, ((S.filter (fun p => p ≤ k)).card : ℝ) * (w (k + 1) - w k) =
        (S.card : ℝ) * w X := by
  classical
  let g : ℕ → ℝ := fun i => if i ∈ S then 1 else 0
  have hsub : S ⊆ Finset.range (X + 1) := by
    intro p hp
    simp only [Finset.mem_range]
    exact Nat.lt_succ_of_le (hbound p hp)
  have hweighted : (∑ i ∈ Finset.range (X + 1), w i * g i) = ∑ p ∈ S, w p := by
    rw [← Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl
      intro p hp
      simp [g, hp]
    · intro i hi hinot
      simp [g, hinot]
  have hpartial (k : ℕ) : (∑ i ∈ Finset.range (k + 1), g i) =
      ((S.filter (fun p => p ≤ k)).card : ℝ) := by
    have hset : (Finset.range (k + 1)).filter (fun i => i ∈ S) =
        S.filter (fun p => p ≤ k) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hi, hp⟩
        exact ⟨hp, by omega⟩
      · rintro ⟨hp, hi⟩
        exact ⟨by omega, hp⟩
    simp only [g, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hset]
  have hS : (∑ i ∈ Finset.range (X + 1), g i) = (S.card : ℝ) := by
    rw [hpartial]
    have heq : S.filter (fun p => p ≤ X) = S := by
      ext p
      simp only [Finset.mem_filter]
      exact ⟨And.left, fun hp => ⟨hp, hbound p hp⟩⟩
    rw [heq]
  have hab := Finset.sum_range_by_parts w g (X + 1)
  simp only [smul_eq_mul, Nat.add_sub_cancel] at hab
  rw [hweighted, hS] at hab
  simp_rw [hpartial] at hab
  have hsum : (∑ k ∈ Finset.range X, ((S.filter (fun p => p ≤ k)).card : ℝ) * (w (k + 1) - w k)) =
      ∑ k ∈ Finset.range X, (w (k + 1) - w k) * ((S.filter (fun p => p ≤ k)).card : ℝ) := by
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hsum]
  linarith

/-- The count of odd primes through each `k≤X` equals the filter of the
odd-prime prefix through `X`. -/
theorem oddPrimePrefix_filter_le {X k : ℕ} (hk : k ≤ X) :
    (oddPrimePrefix X).filter (fun p => p ≤ k) = oddPrimePrefix k := by
  ext p
  simp only [oddPrimePrefix, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨⟨_, hp, hne⟩, hpk⟩
    exact ⟨by omega, hp, hne⟩
  · rintro ⟨hpk, hp, hne⟩
    exact ⟨⟨by omega, hp, hne⟩, by omega⟩

/-- The exact odd-prime prefix through the prescribed maximum has `n²`
entries, including the empty pool at `n=0`. -/
theorem oddPrimePrefix_poolMaximum_card (n : ℕ) :
    (oddPrimePrefix (poolMaximum n)).card = n * n := by
  let f : Fin (n * n) → ℕ := fun i => oddPrime i.val
  have hinj : Function.Injective f := fun i j h => Fin.ext (oddPrime_injective h)
  have hset : Finset.univ.image f = oddPrimePrefix (poolMaximum n) := by
    ext p
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    change (∃ i : Fin (n * n), f i = p) ↔ p ∈ (oddPrimePrefix (poolMaximum n) : Set ℕ)
    exact Set.ext_iff.mp (pool_eq_prefix n) p
  rw [← hset, Finset.card_image_of_injective _ hinj]
  simp

/-- An arbitrary real weight over the exact odd-prime input prefix is
expressed through the actual odd-prime counting function at every integer
below the maximum. -/
theorem oddPrimePool_weighted_partial_summation (n : ℕ) (w : ℕ → ℝ) :
    (∑ p ∈ oddPrimePrefix (poolMaximum n), w p) +
      ∑ k ∈ Finset.range (poolMaximum n), ((oddPrimePrefix k).card : ℝ) * (w (k + 1) - w k) =
        ((n * n : ℕ) : ℝ) * w (poolMaximum n) := by
  have h := finite_count_partial_summation (oddPrimePrefix (poolMaximum n))
    (poolMaximum n) w (by
      intro p hp
      simp only [oddPrimePrefix, Finset.mem_filter, Finset.mem_range] at hp
      omega)
  rw [oddPrimePrefix_poolMaximum_card] at h
  have hsum : (∑ k ∈ Finset.range (poolMaximum n),
      (((oddPrimePrefix (poolMaximum n)).filter (fun p => p ≤ k)).card : ℝ) * (w (k + 1) - w k)) =
      ∑ k ∈ Finset.range (poolMaximum n), ((oddPrimePrefix k).card : ℝ) * (w (k + 1) - w k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [oddPrimePrefix_filter_le (Finset.mem_range.mp hk).le]
  rw [hsum] at h
  exact h

/-- Exact discrete partial summation for the source total `T`: the sum of
odd-prime counts below `X` and the pool sum together equal `n²X`. This
identity includes the final prime and omits prime two exactly. -/
theorem oddPrimePool_total_count_identity (n : ℕ) :
    (Lucas.poolTotal n : ℝ) +
      ∑ k ∈ Finset.range (poolMaximum n), ((oddPrimePrefix k).card : ℝ) =
        ((n * n : ℕ) : ℝ) * (poolMaximum n : ℝ) := by
  have h := oddPrimePool_weighted_partial_summation n (fun p => (p : ℝ))
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_left, mul_one] at h
  rw [poolTotal_eq_prefix_sum]
  push_cast
  simpa only [Nat.cast_mul] using h

end
end Sude
