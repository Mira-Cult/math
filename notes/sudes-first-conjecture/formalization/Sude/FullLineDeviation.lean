import Sude.FullLineCenteredIdentity

/-! Transfer a centered midpoint bound to each actual complete line. -/
namespace Sude
noncomputable section

/-- A centered midpoint bound controls the exact full line after subtracting
its explicit stage means, signed pair gaps, and every residual-cell entry.
The residual sum is retained rather than assumed small. -/
theorem fullLine_deviation_le_centered_bound {m P Q n : ℕ} (hQ : 0 < Q)
    (cells : (Fin P × Fin Q) × Bool → Cell n) (hcells : Function.Injective cells)
    (lines : Fin m → Finset (Cell n)) (a : Cell n ≃ Fin (n * n))
    (weights : Fin m → Fin P → Fin Q → ℝ) (values : Fin P → Fin Q → ℝ)
    (ω : Fin P → Equiv.Perm (Fin Q)) (gap B : ℝ)
    (hweight : ∀ l j q, physicalPairLineWeight cells (fun c => c ∈ lines l) (j, q) = weights l j q)
    (hmid : ∀ j q, (((entry a (cells ((j, q), false)) : ℝ) +
      entry a (cells ((j, q), true))) / 2) = values j (ω j q))
    (hgap : ∀ j q, (entry a (cells ((j, q), true)) : ℝ) -
      entry a (cells ((j, q), false)) = gap)
    (hbound : ∀ l, |stageLineCentered (fun _ _ => Finset.univ) weights values l ω| ≤ B)
    (l : Fin m) :
    |(∑ c ∈ lines l, (entry a c : ℝ)) -
      (∑ c ∈ lines l \ Finset.univ.image cells, (entry a c : ℝ)) -
      (∑ j, ((∑ q, weights l j q) * ((∑ q, values j q) / (Q : ℝ)))) -
      (∑ p, physicalPairLineOrientation cells (fun c => c ∈ lines l) p * (gap / 2))| ≤ B := by
  classical
  have h := fullLine_sum_eq_centered_and_residual hQ cells hcells lines a weights values ω gap
    hweight hmid hgap l
  have heq : (∑ c ∈ lines l, (entry a c : ℝ)) -
      (∑ c ∈ lines l \ Finset.univ.image cells, (entry a c : ℝ)) -
      (∑ j, ((∑ q, weights l j q) * ((∑ q, values j q) / (Q : ℝ)))) -
      (∑ p, physicalPairLineOrientation cells (fun c => c ∈ lines l) p * (gap / 2)) =
      stageLineCentered (fun _ _ => Finset.univ) weights values l ω := by linarith
  rw [heq]
  exact hbound l

end
end Sude
