import Sude.NarrowSeedBounds
import Sude.RegularBlockBalance

/-! NS1–NS4 for consecutive groups from the actual sorted candidate values. -/
namespace Sude
noncomputable section

/-- Consecutive equal-sized groups from an ordered candidate list have total
width at most the list's ambient width. Group endpoints are actual values. -/
theorem sorted_seed_group_widths (w : ℕ → ℝ) (r Q : ℕ) (L U : ℝ)
    (hQ : 0 < Q) (hLU : L ≤ U)
    (hsorted : ∀ i j, i ≤ j → j < r * Q → w i ≤ w j)
    (hbound : ∀ i < r * Q, L ≤ w i ∧ w i ≤ U) :
    (∀ j < r, 0 ≤ w (j * Q + (Q - 1)) - w (j * Q)) ∧
    (∑ j ∈ Finset.range r, (w (j * Q + (Q - 1)) - w (j * Q))) ≤ U - L := by
  have htop : ∀ j < r, j * Q + (Q - 1) < r * Q := by
    intro j hj
    have hm := Nat.mul_le_mul_right Q (show j + 1 ≤ r by omega)
    simp only [Nat.add_mul, one_mul] at hm
    omega
  have hnonneg : ∀ j < r, 0 ≤ w (j * Q + (Q - 1)) - w (j * Q) := by
    intro j hj
    have h := hsorted (j * Q) (j * Q + (Q - 1)) (by omega) (htop j hj)
    linarith
  have hsep : ∀ i j, i < j → j < r → w (i * Q + (Q - 1)) ≤ w (j * Q) := by
    intro i j hij hj
    have hm := Nat.mul_le_mul_right Q (show i + 1 ≤ j by omega)
    simp only [Nat.add_mul, one_mul] at hm
    exact hsorted _ _ (by omega) (by have := htop j hj; omega)
  exact ⟨hnonneg, ordered_block_ranges_le (fun j => w (j * Q))
    (fun j => w (j * Q + (Q - 1))) r L U hLU
    (by intro j hj; exact (hbound _ (by have := htop j hj; omega)).1)
    (by intro j hj; exact (hbound _ (htop j hj)).2) hsep⟩

/-- Select `s` narrowest actual sorted groups and derive the source NS4
variance coefficient, with no sampled or independent-trial assumption. -/
theorem sorted_seed_narrowest_variance (w : ℕ → ℝ) (Q s t : ℕ) (L U d : ℝ)
    (hQ : 0 < Q) (hs : 0 < s) (ht : 2 ≤ t) (hd : 0 ≤ d) (hLU : L ≤ U)
    (hsorted : ∀ i j, i ≤ j → j < (s + t - 1) * Q → w i ≤ w j)
    (hbound : ∀ i < (s + t - 1) * Q, L ≤ w i ∧ w i ≤ U) :
    ∃ kept : Finset ℕ, kept ⊆ Finset.range (s + t - 1) ∧ kept.card = s ∧
      ∃ z : ℝ, (∃ i ∈ kept, z = w (i * Q + (Q - 1)) - w (i * Q)) ∧
        (∀ i ∈ kept, w (i * Q + (Q - 1)) - w (i * Q) ≤ z) ∧
        3 * d * (∑ i ∈ kept, (w (i * Q + (Q - 1)) - w (i * Q)) ^ 2) + 4 * z ^ 2 ≤
          (3 * d / (4 * ((t : ℝ) - 1)) + 4 / (t : ℝ) ^ 2) * (U - L) ^ 2 := by
  let r := s + t - 1
  let width : ℕ → ℝ := fun i => w (i * Q + (Q - 1)) - w (i * Q)
  have hwidth := sorted_seed_group_widths w r Q L U hQ hLU hsorted hbound
  exact narrowest_seed_variance_bound (Finset.range r) width (U - L) d s t hs ht hd
    (by simp [r]) (by intro i hi; exact hwidth.1 i (Finset.mem_range.mp hi)) hwidth.2

end
end Sude
