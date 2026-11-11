import Sude.ActualUnusedKeepoutMean

/-! Exact line-level correction when a role reservation is enlarged to a
full keepout. No numerical line, prime, or diagonal estimate is asserted. -/
namespace Sude
noncomputable section

/-- The algebraic line identity for arbitrary supplied means. It includes
every actual entry of the additional reserved cells on the given line. -/
theorem keepout_line_ideal_difference {n : ℕ}
    (a : Cell n ≃ Fin (n * n)) (roles full line : Finset (Cell n))
    (hsub : roles ⊆ full) (μrole μfull : ℝ) :
    ((∑ c ∈ line ∩ full, (entry a c : ℝ)) + ((line \ full).card : ℝ) * μfull) -
      ((∑ c ∈ line ∩ roles, (entry a c : ℝ)) + ((line \ roles).card : ℝ) * μrole) =
    (∑ c ∈ (full \ roles) ∩ line, ((entry a c : ℝ) - μrole)) +
      ((line \ full).card : ℝ) * (μfull - μrole) := by
  classical
  let extra := (full \ roles) ∩ line
  have hparts : (line ∩ roles) ∪ extra = line ∩ full := by
    ext c
    simp only [extra, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    have hh : c ∈ roles → c ∈ full := fun hc => hsub hc
    tauto
  have hdisj : Disjoint (line ∩ roles) extra := by
    apply Finset.disjoint_left.mpr
    intro c hc he
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp he).1).2 (Finset.mem_inter.mp hc).2
  have hremaining : (line \ full) ∪ extra = line \ roles := by
    ext c
    simp only [extra, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    have hh : c ∈ roles → c ∈ full := fun hc => hsub hc
    tauto
  have hremdisj : Disjoint (line \ full) extra := by
    apply Finset.disjoint_left.mpr
    intro c hc he
    exact (Finset.mem_sdiff.mp hc).2 (Finset.mem_sdiff.mp (Finset.mem_inter.mp he).1).1
  have hcard : (line \ roles).card = (line \ full).card + extra.card := by
    rw [← hremaining, Finset.card_union_of_disjoint hremdisj]
  have hsum : (∑ c ∈ line ∩ full, (entry a c : ℝ)) =
      (∑ c ∈ line ∩ roles, (entry a c : ℝ)) + ∑ c ∈ extra, (entry a c : ℝ) := by
    rw [← hparts, Finset.sum_union hdisj]
  change _ = (∑ c ∈ extra, ((entry a c : ℝ) - μrole)) + _
  rw [hsum, Finset.sum_sub_distrib, hcard]
  simp only [Finset.sum_const, nsmul_eq_mul]
  push_cast
  ring

/-- With a nonempty full-unused pool, both displayed means refer to nonempty
actual unused pools, and the exact line correction follows. -/
theorem actualUnusedPool_line_ideal_difference {n : ℕ}
    (a : Cell n ≃ Fin (n * n)) (roles full line : Finset (Cell n))
    (hsub : roles ⊆ full) (hpos : 0 < (actualUnusedPool a full).card) :
    0 < (actualUnusedPool a roles).card ∧
    ((∑ c ∈ line ∩ full, (entry a c : ℝ)) + ((line \ full).card : ℝ) *
        centralEntriesMean (actualUnusedPool a full) (fun v : pool n => (v.val : ℝ))) -
      ((∑ c ∈ line ∩ roles, (entry a c : ℝ)) + ((line \ roles).card : ℝ) *
        centralEntriesMean (actualUnusedPool a roles) (fun v : pool n => (v.val : ℝ))) =
    (∑ c ∈ (full \ roles) ∩ line,
      ((entry a c : ℝ) - centralEntriesMean (actualUnusedPool a roles) (fun v : pool n => (v.val : ℝ)))) +
      ((line \ full).card : ℝ) *
        (centralEntriesMean (actualUnusedPool a full) (fun v : pool n => (v.val : ℝ)) -
          centralEntriesMean (actualUnusedPool a roles) (fun v : pool n => (v.val : ℝ))) := by
  have hsubset : actualUnusedPool a full ⊆ actualUnusedPool a roles := by
    rw [actualUnusedPool_full_eq_roles_sdiff a roles full hsub]
    exact Finset.sdiff_subset
  refine ⟨lt_of_lt_of_le hpos (Finset.card_le_card hsubset), ?_⟩
  exact keepout_line_ideal_difference a roles full line hsub _ _

end
end Sude
