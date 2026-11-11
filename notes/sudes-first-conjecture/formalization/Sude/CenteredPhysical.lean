import Sude.CenteredGrid
import Sude.PairReservoir

/-! A fixed physical midpoint orientation with a two-sided correction grid.
This is one reservoir, not an existence theorem for graph flows. -/
namespace Sude
noncomputable section

/-- A single reference placement supports every even transfer within the
centered grid. Each target placement is an actual exact-pool permutation,
with all columns, both diagonals and reservations unchanged relative to the
reference. The original pairs and complete grid remain explicit hypotheses. -/
theorem vertical_centered_reference {n P : ℕ} (a : Cell n ≃ Fin (n * n))
    (v : VerticalPairSystem a P) (reserved : Finset (Cell n))
    (hreserved : ∀ k, k < P → ∀ c ∈ reserved,
      c ≠ (v.lowRow, v.column k) ∧ c ≠ (v.highRow, v.column k))
    (labels : Finset ℕ) (hlabels : labels ⊆ Finset.range P) (R : ℕ)
    (hgrid : CompleteEvenGrid labels v.gap R) :
    ∃ (S₀ : Finset ℕ) (b₀ : Cell n ≃ Fin (n * n)),
      S₀ ⊆ labels ∧ ((∑ k ∈ S₀, v.gap k : ℕ) : ℤ) = evenGridCenter R ∧
      VerticalOutcome v reserved S₀ b₀ ∧
      (∀ t : ℤ, (2 : ℤ) ∣ t → -(evenGridCenter R : ℤ) ≤ t →
        t ≤ evenGridCenter R →
        ∃ (S : Finset ℕ) (b : Cell n ≃ Fin (n * n)),
          S ⊆ labels ∧ VerticalOutcome v reserved S b ∧
          (∀ r, (rowSum b r : ℤ) - (rowSum b₀ r : ℤ) =
            (if v.lowRow = r then t else 0) - (if v.highRow = r then t else 0)) ∧
          (∀ c, columnSum b c = columnSum b₀ c) ∧
          mainSum b = mainSum b₀ ∧ antiSum b = antiSum b₀ ∧
          (∀ c ∈ reserved, entry b c = entry b₀ c) ∧
          Set.range (entry b) = pool n ∧ Function.Injective (entry b)) := by
  obtain ⟨S₀, hS₀, hsum₀⟩ := centered_even_grid labels v.gap R hgrid 0 (by norm_num) (by omega) (by omega)
  obtain ⟨b₀, hb₀⟩ := verticalPairs_toggle_subset a v reserved hreserved S₀ (hS₀.trans hlabels)
  have hcenter : ((∑ k ∈ S₀, v.gap k : ℕ) : ℤ) = evenGridCenter R := by omega
  refine ⟨S₀, b₀, hS₀, hcenter, hb₀, ?_⟩
  intro t ht hlow hhigh
  obtain ⟨S, hS, hsum⟩ := centered_even_grid labels v.gap R hgrid t ht hlow hhigh
  obtain ⟨b, hb⟩ := verticalPairs_toggle_subset a v reserved hreserved S (hS.trans hlabels)
  have hsum₀' : (∑ k ∈ S₀, (v.gap k : ℤ)) - evenGridCenter R = 0 := by
    exact_mod_cast hsum₀
  have hsum' : (∑ k ∈ S, (v.gap k : ℤ)) - evenGridCenter R = t := by
    exact_mod_cast hsum
  refine ⟨S, b, hS, hb, ?_, ?_, ?_, ?_, ?_, entry_range _, entry_injective _⟩
  · intro r
    have h₀ := hb₀.rows r
    have h₁ := hb.rows r
    split_ifs at h₀ h₁ ⊢ <;> omega
  · intro c
    exact (hb.columns c).trans (hb₀.columns c).symm
  · exact hb.main.trans hb₀.main.symm
  · exact hb.anti.trans hb₀.anti.symm
  · intro c hc
    exact (hb.reserved_fixed c hc).trans (hb₀.reserved_fixed c hc).symm

end
end Sude
