import Sude.PrefixStageCertificate

/-! Separation of actual certified endpoint footprints by interval bounds. -/
namespace Sude

/-- Both endpoints of every certified pair remain in the stated interval,
including the gap on the upper endpoint. -/
theorem PrefixStageBlock.footprint_bounds {gap bound lo hi : ℕ} {xs : List ℕ}
    (hstage : PrefixStageBlock gap bound lo hi xs) {x : ℕ}
    (hx : x ∈ pairFootprint xs.toFinset gap) : lo ≤ x ∧ x ≤ hi + gap := by
  rcases Finset.mem_union.mp hx with hx | hx
  · have h := hstage.entries x (List.mem_toFinset.mp hx)
    omega
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    have h := hstage.entries p (List.mem_toFinset.mp hp)
    omega

/-- Certified endpoint intervals that do not overlap give genuine
cross-stage separation, without testing or assuming distinct entries. -/
theorem PrefixStageBlock.footprints_disjoint
    {gap₁ gap₂ bound₁ bound₂ lo₁ hi₁ lo₂ hi₂ : ℕ} {xs ys : List ℕ}
    (h₁ : PrefixStageBlock gap₁ bound₁ lo₁ hi₁ xs)
    (h₂ : PrefixStageBlock gap₂ bound₂ lo₂ hi₂ ys) (hsep : hi₁ + gap₁ < lo₂) :
    Disjoint (pairFootprint xs.toFinset gap₁) (pairFootprint ys.toFinset gap₂) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hleft := h₁.footprint_bounds hx
  have hright := h₂.footprint_bounds hy
  omega

end Sude
