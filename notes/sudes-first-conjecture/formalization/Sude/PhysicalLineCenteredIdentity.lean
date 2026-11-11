import Sude.PhysicalPairLineSum
import Sude.StageLineSumIdentity

/-! Link a centered stage variable to a line sum on actual physical cells. -/
namespace Sude
noncomputable section

/-- For disjoint physical pairs whose endpoints have the given midpoints
and fixed gap, the sum over actual selected cells is the centered stage
variable plus explicit mean and orientation terms. The unselected cells
remain a separate obligation. -/
theorem physicalPair_line_sum_eq_centered {m P Q n : ℕ} (hQ : 0 < Q)
    (cells : (Fin P × Fin Q) × Bool → Cell n) (hcells : Function.Injective cells)
    (line : Fin m → Cell n → Prop) [∀ l, DecidablePred (line l)]
    (a : Cell n ≃ Fin (n * n)) (weights : Fin m → Fin P → Fin Q → ℝ)
    (values : Fin P → Fin Q → ℝ) (ω : Fin P → Equiv.Perm (Fin Q)) (gap : ℝ)
    (hweight : ∀ l j q, physicalPairLineWeight cells (line l) (j, q) = weights l j q)
    (hmid : ∀ j q, (((entry a (cells ((j, q), false)) : ℝ) +
      entry a (cells ((j, q), true))) / 2) = values j (ω j q))
    (hgap : ∀ j q, (entry a (cells ((j, q), true)) : ℝ) -
      entry a (cells ((j, q), false)) = gap) (l : Fin m) :
    (∑ c ∈ (Finset.univ.image cells).filter (line l), (entry a c : ℝ)) =
      stageLineCentered (fun _ _ => Finset.univ) weights values l ω +
      (∑ j, ((∑ q, weights l j q) * ((∑ q, values j q) / (Q : ℝ)))) +
      ∑ p, physicalPairLineOrientation cells (line l) p * (gap / 2) := by
  classical
  rw [physicalPair_line_sum_midpoint cells hcells (line l) a]
  simp_rw [Finset.sum_add_distrib]
  congr 1
  · rw [Fintype.sum_prod_type]
    simp_rw [hweight, hmid]
    exact stageLineWeightedSum_eq_centered_add_mean hQ weights values l ω
  · apply Finset.sum_congr rfl
    rintro ⟨j, q⟩ _
    rw [hgap j q]

end
end Sude
