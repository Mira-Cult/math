import Sude.CentralWindow

/-! One-depth parent/child mean accounting for simultaneous prefix rounding.
This algebra does not construct any partition, rounding or assignment. -/
namespace Sude
noncomputable section

/-- A parent mean with child totals of sizes `m` and `q-m` is their
weighted average. The nonempty parent and the cardinality relation are
explicit. -/
theorem prefix_parent_mean_from_child_totals (q m : ℕ) (mean low high : ℝ)
    (hq : 0 < q) (hm : m ≤ q)
    (htotal : (q : ℝ) * mean = (m : ℝ) * low + ((q - m : ℕ) : ℝ) * high) :
    mean = ((m : ℝ) / q) * low + (1 - (m : ℝ) / q) * high := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hsub : ((q - m : ℕ) : ℝ) = (q : ℝ) - m := by exact Nat.cast_sub hm
  rw [hsub] at htotal
  field_simp
  nlinarith

/-- The parent conditional mean is the weighted average of its two child
means; the deviation in a line's child contribution is the signed rounding
error in its lower-child slot weight. -/
theorem prefix_parent_child_mean_identity (K Kleft low high ratio mean : ℝ)
    (hmean : mean = ratio * low + (1 - ratio) * high) :
    Kleft * low + (K - Kleft) * high - K * mean =
      -(high - low) * (Kleft - ratio * K) := by
  rw [hmean]
  ring

/-- Summed over all slots at a single depth, the change in a line's
conditional mean equals one global weighted rounding error. Different groups
may have different means, split ratios and mean gaps; their errors are not
bounded separately. -/
theorem prefix_depth_mean_identity {S G : Type*}
    (U : Finset S) (group : S → G) (left : S → Bool)
    (w : S → ℝ) (low high ratio mean : G → ℝ)
    (hmean : ∀ s ∈ U, mean (group s) =
      ratio (group s) * low (group s) + (1 - ratio (group s)) * high (group s)) :
    (∑ s ∈ U, w s * (if left s then low (group s) else high (group s))) -
      (∑ s ∈ U, w s * mean (group s)) =
    -(∑ s ∈ U, w s * (high (group s) - low (group s)) *
      ((if left s then (1 : ℝ) else 0) - ratio (group s))) := by
  classical
  rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  rw [hmean s hs]
  cases left s <;> simp <;> ring

/-- A bound for the one global rounding error transfers unchanged to the
change in conditional mean at this depth. -/
theorem prefix_depth_mean_bound {S G : Type*}
    (U : Finset S) (group : S → G) (left : S → Bool)
    (w : S → ℝ) (low high ratio mean : G → ℝ) (B : ℝ)
    (hmean : ∀ s ∈ U, mean (group s) =
      ratio (group s) * low (group s) + (1 - ratio (group s)) * high (group s))
    (hbound : |∑ s ∈ U, w s * (high (group s) - low (group s)) *
      ((if left s then (1 : ℝ) else 0) - ratio (group s))| ≤ B) :
    |(∑ s ∈ U, w s * (if left s then low (group s) else high (group s))) -
      (∑ s ∈ U, w s * mean (group s))| ≤ B := by
  rw [prefix_depth_mean_identity U group left w low high ratio mean hmean, abs_neg]
  exact hbound

end
end Sude
