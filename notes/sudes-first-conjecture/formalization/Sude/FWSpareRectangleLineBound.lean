import Sude.SpareRectangleLineSeparation
import Sude.PackedRectangleCenteredLineBound

/-! Per-row and per-column bounds for actual unused rectangle corners.
The separate change of unused-pool mean in a keepout-line identity is not
bounded here. No diagonal or full-line discrepancy is asserted. -/
namespace Sude
noncomputable section

/-- Every row and column contains zero or two actual spare rectangle corners.
Under the supplied value and mean bounds, their centered sum has magnitude at
most `257X/250`. The complete rectangle choice is shared throughout. -/
theorem fw_spare_rectangle_centered_row_column_bound {n P : ℕ} (hP : P ≤ 238)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (a : Cell n ≃ Fin (n*n)) (X μ : ℝ) (hX : 0 ≤ X)
    (hvalues : ∀ c : Cell n, 0 ≤ (entry a c : ℝ) ∧ (entry a c : ℝ) ≤ X)
    (hlo : (243 / 500 : ℝ) * X ≤ μ) (hhi : μ ≤ (123 / 250 : ℝ) * X) :
    let spare := packedRectangleSupport hs choice \ activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)
    (∀ r : Fin n,
      ((LayerPacking.rowUsed spare r).card = 0 ∨ (LayerPacking.rowUsed spare r).card = 2) ∧
      |∑ c ∈ LayerPacking.rowUsed spare r, ((entry a (r,c) : ℝ) - μ)| ≤ (257 / 250 : ℝ) * X) ∧
    (∀ c : Fin n,
      ((LayerPacking.colUsed spare c).card = 0 ∨ (LayerPacking.colUsed spare c).card = 2) ∧
      |∑ r ∈ LayerPacking.colUsed spare c, ((entry a (r,c) : ℝ) - μ)| ≤ (257 / 250 : ℝ) * X) := by
  classical
  dsimp only
  obtain ⟨_, hrows, hcols, hspare⟩ := fw_spare_rectangle_line_separation hP hs choice
  constructor
  · intro r
    have hc : (LayerPacking.rowUsed
        (packedRectangleSupport hs choice \ activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)) r).card = 0 ∨
        (LayerPacking.rowUsed
        (packedRectangleSupport hs choice \ activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)) r).card = 2 := by
      rw [hspare]
      exact hrows r
    refine ⟨hc, ?_⟩
    have hcard : (LayerPacking.rowUsed
        (packedRectangleSupport hs choice \ activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)) r).card ≤ 2 := by
      rcases hc with h | h <;> omega
    exact two_values_centered_sum_bound _ (fun c => (entry a (r,c) : ℝ)) X μ hX hcard
      (fun c _ => hvalues (r,c)) hlo hhi
  · intro c
    have hc : (LayerPacking.colUsed
        (packedRectangleSupport hs choice \ activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)) c).card = 0 ∨
        (LayerPacking.colUsed
        (packedRectangleSupport hs choice \ activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)) c).card = 2 := by
      rw [hspare]
      exact hcols c
    refine ⟨hc, ?_⟩
    have hcard : (LayerPacking.colUsed
        (packedRectangleSupport hs choice \ activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)) c).card ≤ 2 := by
      rcases hc with h | h <;> omega
    exact two_values_centered_sum_bound _ (fun r => (entry a (r,c) : ℝ)) X μ hX hcard
      (fun r _ => hvalues (r,c)) hlo hhi

end
end Sude
