import Sude.ActualUnusedKeepoutLineIdeal

/-! Exact coupled role-to-full line accounting on one square. This identity
is an alternative representation of the spare correction; it is not an
additional charge on top of a full-reservation cancellation formula. -/
namespace Sude
noncomputable section

/-- Split actual spare cells into those on and off the line before applying
the exact unused-mean update. No numerical or line-discrepancy bound is made. -/
theorem actual_unused_keepout_coupled_line_identity {n : ℕ}
    (a : Cell n ≃ Fin (n*n)) (roles full line : Finset (Cell n))
    (hsub : roles ⊆ full) (hpos : 0 < (actualUnusedPool a full).card) :
    let μr := centralEntriesMean (actualUnusedPool a roles) (fun v : pool n => (v.val : ℝ))
    let μf := centralEntriesMean (actualUnusedPool a full) (fun v : pool n => (v.val : ℝ))
    let E := full \ roles
    let M : ℝ := (actualUnusedPool a full).card
    let k : ℝ := (line \ full).card
    let onLine := ∑ c ∈ E ∩ line, ((entry a c : ℝ) - μr)
    let offLine := ∑ c ∈ E \ line, ((entry a c : ℝ) - μr)
    ((∑ c ∈ line ∩ full, (entry a c : ℝ)) + ((line \ full).card : ℝ) * μf) -
      ((∑ c ∈ line ∩ roles, (entry a c : ℝ)) + ((line \ roles).card : ℝ) * μr) =
      (1 - k / M) * onLine - (k / M) * offLine := by
  classical
  dsimp only
  let μr := centralEntriesMean (actualUnusedPool a roles) (fun v : pool n => (v.val : ℝ))
  let μf := centralEntriesMean (actualUnusedPool a full) (fun v : pool n => (v.val : ℝ))
  let E := full \ roles
  let M : ℝ := (actualUnusedPool a full).card
  let k : ℝ := (line \ full).card
  let onLine := ∑ c ∈ E ∩ line, ((entry a c : ℝ) - μr)
  let offLine := ∑ c ∈ E \ line, ((entry a c : ℝ) - μr)
  have hpartition : (∑ c ∈ E, ((entry a c : ℝ) - μr)) = onLine + offLine := by
    dsimp [onLine, offLine]
    exact (Finset.sum_inter_add_sum_sdiff E line _).symm
  have hmean : μf - μr = -(onLine + offLine) / M := by
    have h := actualUnusedPool_full_mean_eq_roles_mean_sub_extra a roles full hsub hpos
    change μf = μr - ((∑ c ∈ E, (entry a c : ℝ)) - (E.card : ℝ) * μr) / M at h
    have hsum : (∑ c ∈ E, (entry a c : ℝ)) - (E.card : ℝ) * μr = onLine + offLine := by
      rw [← hpartition, Finset.sum_sub_distrib]
      simp
    rw [hsum] at h
    rw [h]
    ring
  have hline := keepout_line_ideal_difference a roles full line hsub μr μf
  change ((∑ c ∈ line ∩ full, (entry a c : ℝ)) + k * μf) -
      ((∑ c ∈ line ∩ roles, (entry a c : ℝ)) + ((line \ roles).card : ℝ) * μr) =
      onLine + k * (μf - μr) at hline
  change ((∑ c ∈ line ∩ full, (entry a c : ℝ)) + k * μf) -
      ((∑ c ∈ line ∩ roles, (entry a c : ℝ)) + ((line \ roles).card : ℝ) * μr) =
      (1 - k / M) * onLine - (k / M) * offLine
  rw [hline, hmean]
  ring

end
end Sude
