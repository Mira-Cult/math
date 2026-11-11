import Sude.ActualUnusedKeepoutMean

/-! Bound the change between actual role-relative and full-keepout unused
means on one square. The full signed-cancellation formula already includes
the spare contribution, so this is not an additional charge to that formula. -/
namespace Sude
noncomputable section

/-- A bound on the spare cells' deviation from a supplied reference mean and
on the role-unused mean's deviation from that reference controls the actual
full-minus-role unused-mean shift. The denominator is the positive actual
full-unused count; no geometry or numerical bound is inferred. -/
theorem actual_unused_full_mean_shift_bound {n : ℕ}
    (a : Cell n ≃ Fin (n*n)) (roles full : Finset (Cell n))
    (hsub : roles ⊆ full) (hpos : 0 < (actualUnusedPool a full).card)
    (μ Dmax Urole : ℝ)
    (hD : |(∑ c ∈ full \ roles, (entry a c : ℝ)) - ((full \ roles).card : ℝ) * μ| ≤ Dmax)
    (hrole : |centralEntriesMean (actualUnusedPool a roles) (fun v : pool n => (v.val : ℝ)) - μ| ≤ Urole) :
    |centralEntriesMean (actualUnusedPool a full) (fun v : pool n => (v.val : ℝ)) -
      centralEntriesMean (actualUnusedPool a roles) (fun v : pool n => (v.val : ℝ))| ≤
      (Dmax + ((full \ roles).card : ℝ) * Urole) / ((actualUnusedPool a full).card : ℝ) := by
  classical
  let mr := centralEntriesMean (actualUnusedPool a roles) (fun v : pool n => (v.val : ℝ))
  let mf := centralEntriesMean (actualUnusedPool a full) (fun v : pool n => (v.val : ℝ))
  let k : ℝ := (full \ roles).card
  let M : ℝ := (actualUnusedPool a full).card
  let D : ℝ := (∑ c ∈ full \ roles, (entry a c : ℝ)) - k * μ
  have hM : 0 < M := by dsimp [M]; exact_mod_cast hpos
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hid : mf - mr = -((D - k * (mr - μ)) / M) := by
    have h := actualUnusedPool_full_mean_eq_roles_mean_sub_extra a roles full hsub hpos
    change mf = mr - ((∑ c ∈ full \ roles, (entry a c : ℝ)) - k * mr) / M at h
    dsimp [D]
    rw [h]
    ring
  change |mf - mr| ≤ (Dmax + k * Urole) / M
  rw [hid, abs_neg, abs_div, abs_of_pos hM]
  apply div_le_div_of_nonneg_right _ hM.le
  calc
    |D - k * (mr - μ)| ≤ |D| + |k * (mr - μ)| := abs_sub D _
    _ = |D| + k * |mr - μ| := by rw [abs_mul, abs_of_nonneg hk]
    _ ≤ Dmax + k * Urole := add_le_add hD (mul_le_mul_of_nonneg_left hrole hk)

end
end Sude
