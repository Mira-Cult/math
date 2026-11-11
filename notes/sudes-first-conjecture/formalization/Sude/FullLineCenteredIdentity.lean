import Sude.PhysicalLineCenteredIdentity
import Sude.LineResidualDecomposition

/-! Retain all residual entries while using the centered selected-pair sum. -/
namespace Sude
noncomputable section

/-- The full labelled line sum consists of the centered selected-pair
variable, its exact mean and orientation terms, and the sum of every
unselected cell on that line. -/
theorem fullLine_sum_eq_centered_and_residual {m P Q n : ℕ} (hQ : 0 < Q)
    (cells : (Fin P × Fin Q) × Bool → Cell n) (hcells : Function.Injective cells)
    (lines : Fin m → Finset (Cell n)) (a : Cell n ≃ Fin (n * n))
    (weights : Fin m → Fin P → Fin Q → ℝ) (values : Fin P → Fin Q → ℝ)
    (ω : Fin P → Equiv.Perm (Fin Q)) (gap : ℝ)
    (hweight : ∀ l j q, physicalPairLineWeight cells (fun c => c ∈ lines l) (j, q) = weights l j q)
    (hmid : ∀ j q, (((entry a (cells ((j, q), false)) : ℝ) +
      entry a (cells ((j, q), true))) / 2) = values j (ω j q))
    (hgap : ∀ j q, (entry a (cells ((j, q), true)) : ℝ) -
      entry a (cells ((j, q), false)) = gap) (l : Fin m) :
    (∑ c ∈ lines l, (entry a c : ℝ)) =
      (stageLineCentered (fun _ _ => Finset.univ) weights values l ω +
       (∑ j, ((∑ q, weights l j q) * ((∑ q, values j q) / (Q : ℝ)))) +
       (∑ p, physicalPairLineOrientation cells (fun c => c ∈ lines l) p * (gap / 2))) +
      ∑ c ∈ lines l \ Finset.univ.image cells, (entry a c : ℝ) := by
  classical
  have hpartition := fullLine_sum_pair_and_residual cells hcells (lines l) a
  have hselected := physicalPair_line_sum_midpoint cells hcells (fun c => c ∈ lines l) a
  rw [← hselected] at hpartition
  rw [hpartition, physicalPair_line_sum_eq_centered hQ cells hcells
    (fun l c => c ∈ lines l) a weights values ω gap hweight hmid hgap l]

end
end Sude
