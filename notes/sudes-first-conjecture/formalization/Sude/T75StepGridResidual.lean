import Sude.StepGrid

/-! An exact target residual from a supplied arbitrary-step subset-sum grid.
No grid, prime pair, or target existence is asserted. -/
namespace Sude

/-- Once the free total and controlled lower total leave a nonnegative,
step-divisible residual within the supplied grid radius, a subset of the
controlled gaps realizes the target exactly. -/
theorem t75_step_grid_exact_residual {α : Type*} (S : Finset α)
    (gap : α → ℕ) (step radius free lower target : ℕ)
    (hgrid : CompleteStepGrid S gap step radius)
    (hlo : free + lower ≤ target) (hhi : target ≤ free + lower + radius)
    (hdiv : step ∣ target - (free + lower)) :
    ∃ chosen : Finset α, chosen ⊆ S ∧
      target = free + lower + ∑ i ∈ chosen, gap i := by
  obtain ⟨chosen, hsub, hsum⟩ := hgrid (target - (free + lower)) (by omega) hdiv
  refine ⟨chosen, hsub, ?_⟩
  omega

end Sude
