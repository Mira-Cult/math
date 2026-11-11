import Sude.ActiveRectangleLineCounts
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! A conditional centered sum bound for the full packed rectangle support.
No role-unused mean, diagonal, or full-line bound is asserted. -/
namespace Sude
noncomputable section

/-- Any at-most-two supplied values in `[0,X]` have centered sum at most
`257X/250` in absolute value under the stated mean interval. -/
theorem two_values_centered_sum_bound {α : Type*} (S : Finset α)
    (v : α → ℝ) (X μ : ℝ) (hX : 0 ≤ X) (hcard : S.card ≤ 2)
    (hvalues : ∀ x ∈ S, 0 ≤ v x ∧ v x ≤ X)
    (hlo : (243 / 500 : ℝ) * X ≤ μ) (hhi : μ ≤ (123 / 250 : ℝ) * X) :
    |∑ x ∈ S, (v x - μ)| ≤ (257 / 250 : ℝ) * X := by
  have hterm : ∀ x ∈ S, |v x - μ| ≤ (257 / 500 : ℝ) * X := by
    intro x hx
    obtain ⟨hl, hu⟩ := hvalues x hx
    apply abs_le.mpr
    constructor <;> linarith
  have hc : (S.card : ℝ) ≤ 2 := by exact_mod_cast hcard
  calc
    |∑ x ∈ S, (v x - μ)| ≤ ∑ x ∈ S, |v x - μ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ S, (257 / 500 : ℝ) * X := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * ((257 / 500 : ℝ) * X) := by simp
    _ ≤ (257 / 250 : ℝ) * X := by nlinarith

/-- Full packed rectangles meet each row and column in at most two cells;
their actual centered entry sums satisfy the stated bound on every line. -/
theorem packed_rectangle_centered_row_column_bound {L n : ℕ}
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (a : Cell n ≃ Fin (n * n)) (X μ : ℝ) (hX : 0 ≤ X)
    (hvalues : ∀ c : Cell n, 0 ≤ (entry a c : ℝ) ∧ (entry a c : ℝ) ≤ X)
    (hlo : (243 / 500 : ℝ) * X ≤ μ) (hhi : μ ≤ (123 / 250 : ℝ) * X) :
    (∀ r : Fin n,
      (LayerPacking.rowUsed (packedRectangleSupport hs choice) r).card ≤ 2 ∧
      |∑ c ∈ LayerPacking.rowUsed (packedRectangleSupport hs choice) r,
        ((entry a (r, c) : ℝ) - μ)| ≤ (257 / 250 : ℝ) * X) ∧
    (∀ c : Fin n,
      (LayerPacking.colUsed (packedRectangleSupport hs choice) c).card ≤ 2 ∧
      |∑ r ∈ LayerPacking.colUsed (packedRectangleSupport hs choice) c,
        ((entry a (r, c) : ℝ) - μ)| ≤ (257 / 250 : ℝ) * X) := by
  classical
  have hall : activeRectangleSupport hs choice Finset.univ = packedRectangleSupport hs choice := by
    simp [activeRectangleSupport, packedRectangleSupport]
  constructor
  · intro r
    have hc : (LayerPacking.rowUsed (packedRectangleSupport hs choice) r).card ≤ 2 := by
      rw [← hall]
      exact active_rectangle_row_load_le_two hs choice Finset.univ r
    refine ⟨hc, ?_⟩
    exact two_values_centered_sum_bound _ (fun c => (entry a (r, c) : ℝ)) X μ hX hc
      (fun c _ => hvalues (r, c)) hlo hhi
  · intro c
    have hc : (LayerPacking.colUsed (packedRectangleSupport hs choice) c).card ≤ 2 := by
      rw [← hall]
      exact active_rectangle_column_load_le_two hs choice Finset.univ c
    refine ⟨hc, ?_⟩
    exact two_values_centered_sum_bound _ (fun r => (entry a (r, c) : ℝ)) X μ hX hc
      (fun r _ => hvalues (r, c)) hlo hhi

end
end Sude
