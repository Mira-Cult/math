import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! The ordered-block range and mean estimates used by RF2 and CC4. -/
namespace Sude

/-- Consecutive, ordered intervals have total width at most the width of the
ambient interval. The assertion also covers an empty list of blocks. -/
theorem ordered_block_ranges_le (lo hi : ℕ → ℝ) (k : ℕ) (L U : ℝ)
    (hLU : L ≤ U) (hlow : ∀ j < k, L ≤ lo j) (hupp : ∀ j < k, hi j ≤ U)
    (hsep : ∀ i j, i < j → j < k → hi i ≤ lo j) :
    (∑ j ∈ Finset.range k, (hi j - lo j)) ≤ U - L := by
  induction k generalizing U with
  | zero => simp only [Finset.range_zero, Finset.sum_empty]; linarith
  | succ k ih =>
    have hk : k < k + 1 := by omega
    have hprev : (∑ j ∈ Finset.range k, (hi j - lo j)) ≤ lo k - L := by
      apply ih (lo k) (hlow k hk)
      · intro j hj
        exact hlow j (by omega)
      · intro j hj
        exact hsep j k hj hk
      · intro i j hij hj
        exact hsep i j hij (by omega)
    rw [Finset.sum_range_succ]
    have hlast := hupp k hk
    linarith

/-- A finite nonempty block's arithmetic mean remains between its endpoint
bounds, with the denominator explicitly positive. -/
theorem finite_block_mean_bounds (v : ℕ → ℝ) (n : ℕ) (hn : 0 < n) (L U : ℝ)
    (hbound : ∀ i < n, L ≤ v i ∧ v i ≤ U) :
    L ≤ (∑ i ∈ Finset.range n, v i) / n ∧
      (∑ i ∈ Finset.range n, v i) / n ≤ U := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlo : (n : ℝ) * L ≤ ∑ i ∈ Finset.range n, v i := by
    calc
      (n : ℝ) * L = ∑ _i ∈ Finset.range n, L := by simp
      _ ≤ ∑ i ∈ Finset.range n, v i := by
        apply Finset.sum_le_sum
        intro i hi
        exact (hbound i (Finset.mem_range.mp hi)).1
  have hhi : (∑ i ∈ Finset.range n, v i) ≤ (n : ℝ) * U := by
    calc
      (∑ i ∈ Finset.range n, v i) ≤ ∑ _i ∈ Finset.range n, U := by
        apply Finset.sum_le_sum
        intro i hi
        exact (hbound i (Finset.mem_range.mp hi)).2
      _ = (n : ℝ) * U := by simp
  constructor
  · exact (le_div_iff₀ hnR).2 (by nlinarith)
  · exact (div_le_iff₀ hnR).2 (by nlinarith)

/-- Picking one value per ordered block differs from the sum of the block
means by no more than the ambient range. No independence is assumed. -/
theorem ordered_blocks_balanced (v : ℕ → ℕ → ℝ) (pick lo hi : ℕ → ℝ)
    (k n : ℕ) (hn : 0 < n) (L U : ℝ) (hLU : L ≤ U)
    (hlow : ∀ j < k, L ≤ lo j) (hupp : ∀ j < k, hi j ≤ U)
    (hsep : ∀ i j, i < j → j < k → hi i ≤ lo j)
    (hblock : ∀ j < k, ∀ i < n, lo j ≤ v j i ∧ v j i ≤ hi j)
    (hpick : ∀ j < k, lo j ≤ pick j ∧ pick j ≤ hi j) :
    |(∑ j ∈ Finset.range k, pick j) -
      ∑ j ∈ Finset.range k, (∑ i ∈ Finset.range n, v j i) / n| ≤ U - L := by
  have hpoint : ∀ j < k,
      |pick j - (∑ i ∈ Finset.range n, v j i) / n| ≤ hi j - lo j := by
    intro j hj
    have hm := finite_block_mean_bounds (v j) n hn (lo j) (hi j) (hblock j hj)
    have hp := hpick j hj
    rw [abs_le]
    constructor <;> linarith
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ j ∈ Finset.range k, (pick j - (∑ i ∈ Finset.range n, v j i) / n)| ≤
        ∑ j ∈ Finset.range k, |pick j - (∑ i ∈ Finset.range n, v j i) / n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range k, (hi j - lo j) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hpoint j (Finset.mem_range.mp hj)
    _ ≤ U - L := ordered_block_ranges_le lo hi k L U hLU hlow hupp hsep

/-- The sum of the `k` block means is exactly `k` times the mean of all
`k*n` entries. Both nonzero denominators are explicit. -/
theorem sum_block_means_eq_global (v : ℕ → ℕ → ℝ) (k n : ℕ)
    (hk : 0 < k) (hn : 0 < n) :
    (∑ j ∈ Finset.range k, (∑ i ∈ Finset.range n, v j i) / n) =
      (k : ℝ) * ((∑ j ∈ Finset.range k, ∑ i ∈ Finset.range n, v j i) /
        ((k * n : ℕ) : ℝ)) := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hk)
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  rw [← Finset.sum_div]
  push_cast
  field_simp

/-- The source's actual consecutive blocks of a sorted `k*n`-entry list
have total discrepancy at most the range of the whole list. Each selected
value comes from its own block; repeated choices across different blocks
are impossible when the underlying list is injective, a separate property. -/
theorem consecutive_sorted_blocks_balanced (w pick : ℕ → ℝ) (k n : ℕ)
    (hk : 0 < k) (hn : 0 < n)
    (hsorted : ∀ i j, i ≤ j → j < k * n → w i ≤ w j)
    (hpick : ∀ j < k, ∃ i < n, pick j = w (j * n + i)) :
    |(∑ j ∈ Finset.range k, pick j) -
      (k : ℝ) * ((∑ j ∈ Finset.range k, ∑ i ∈ Finset.range n, w (j * n + i)) /
        ((k * n : ℕ) : ℝ))| ≤ w (k * n - 1) - w 0 := by
  have hkn : 0 < k * n := Nat.mul_pos hk hn
  have hlast : k * n - 1 < k * n := by omega
  have htop : ∀ j < k, j * n + (n - 1) < k * n := by
    intro j hj
    have hm := Nat.mul_le_mul_right n (show j + 1 ≤ k by omega)
    simp only [Nat.add_mul, one_mul] at hm
    omega
  have hblock : ∀ j < k, ∀ i < n,
      w (j * n) ≤ w (j * n + i) ∧ w (j * n + i) ≤ w (j * n + (n - 1)) := by
    intro j hj i hi
    have ht := htop j hj
    constructor
    · exact hsorted _ _ (by omega) (by omega)
    · exact hsorted _ _ (by omega) ht
  have hsep : ∀ i j, i < j → j < k → w (i * n + (n - 1)) ≤ w (j * n) := by
    intro i j hij hj
    have hm := Nat.mul_le_mul_right n (show i + 1 ≤ j by omega)
    simp only [Nat.add_mul, one_mul] at hm
    have hjtop := htop j hj
    exact hsorted _ _ (by omega) (by omega)
  have hp : ∀ j < k, w (j * n) ≤ pick j ∧ pick j ≤ w (j * n + (n - 1)) := by
    intro j hj
    obtain ⟨i, hi, heq⟩ := hpick j hj
    rw [heq]
    exact hblock j hj i hi
  have hbound := ordered_blocks_balanced (fun j i => w (j * n + i)) pick
    (fun j => w (j * n)) (fun j => w (j * n + (n - 1))) k n hn
    (w 0) (w (k * n - 1)) (hsorted 0 _ (by omega) hlast)
    (by intro j hj; exact hsorted 0 _ (by omega) (by have := htop j hj; omega))
    (by intro j hj; exact hsorted _ _ (by have := htop j hj; omega) hlast)
    hsep hblock hp
  rw [sum_block_means_eq_global _ k n hk hn] at hbound
  exact hbound

end Sude
