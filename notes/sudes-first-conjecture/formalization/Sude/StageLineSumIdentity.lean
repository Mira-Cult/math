import Sude.StageLineExplicitMean

/-! Reassemble the actual weighted midpoint sum from the centered variable. -/
namespace Sude
noncomputable section

/-- With every slot occupied, the centered probability variable plus its
explicit stage means is the actual weighted sum, for each labelled line. -/
theorem stageLineWeightedSum_eq_centered_add_mean {m P Q : ℕ} (hQ : 0 < Q)
    (weights : Fin m → Fin P → Fin Q → ℝ) (values : Fin P → Fin Q → ℝ)
    (l : Fin m) (ω : Fin P → Equiv.Perm (Fin Q)) :
    (∑ j, ∑ q, weights l j q * values j (ω j q)) =
      stageLineCentered (fun _ _ => Finset.univ) weights values l ω +
      ∑ j, ((∑ q, weights l j q) * ((∑ q, values j q) / (Q : ℝ))) := by
  rw [stageLineCentered_eq_explicit_mean hQ]
  simp only [Finset.sum_sub_distrib]
  ring

end
end Sude
