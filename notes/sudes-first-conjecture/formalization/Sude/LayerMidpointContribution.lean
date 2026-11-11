import Sude.LayerIncidenceInvoice

/-! Actual physical pair contributions split into midpoint and orientation. -/
namespace Sude.LayerPacking
noncomputable section

/-- The contribution of an oriented physical pair to a row. -/
def pairRowContribution {n : ℕ} (π f : Equiv.Perm (Fin n)) (r i : Fin n)
    (low high : ℝ) : ℝ :=
  (if (layerCell π f (i, false)).1 = r then low else 0) +
    (if (layerCell π f (i, true)).1 = r then high else 0)

/-- The signed incidence of the high endpoint minus the low endpoint. -/
def layerRowOrientation {n : ℕ} (π f : Equiv.Perm (Fin n)) (r i : Fin n) : ℝ :=
  (if (layerCell π f (i, true)).1 = r then 1 else 0) -
    (if (layerCell π f (i, false)).1 = r then 1 else 0)

/-- The identity retains the full high/low orientation; it is valid for
any actual pair values and any incidences, including zero or two hits. -/
theorem pairRowContribution_midpoint {n : ℕ} (π f : Equiv.Perm (Fin n))
    (r i : Fin n) (low high : ℝ) :
    pairRowContribution π f r i low high =
      layerRowWeight π f r i * ((low + high) / 2) +
        layerRowOrientation π f r i * ((high - low) / 2) := by
  unfold pairRowContribution layerRowWeight layerRowOrientation
  by_cases h₀ : (layerCell π f (i, false)).1 = r <;>
    by_cases h₁ : (layerCell π f (i, true)).1 = r <;>
    simp [h₀, h₁] <;> ring

/-- If every pair has a common gap, the orientation contribution is fixed
while the midpoint terms may be permuted between pair slots. -/
theorem layerRowContribution_midpoint {n : ℕ} (π f : Equiv.Perm (Fin n))
    (r : Fin n) (low high : Fin n → ℝ) (gap : ℝ)
    (hgap : ∀ i, high i - low i = gap) :
    (∑ i, pairRowContribution π f r i (low i) (high i)) =
      (∑ i, layerRowWeight π f r i * ((low i + high i) / 2)) +
      (∑ i, layerRowOrientation π f r i * (gap / 2)) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [pairRowContribution_midpoint, hgap i]

end
end Sude.LayerPacking
