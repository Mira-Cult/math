import Sude.GrowthPhysicalEntryBudget

/-! Eliminating the signed stage-gap invoice under a supplied stagewise
orientation cancellation. This does not prove cancellation or bound the
residual cells. -/
namespace Sude
noncomputable section

/-- A stage-dependent half-gap invoice vanishes when the unweighted signed
orientations cancel separately within every stage. Gaps may vary by stage. -/
theorem stage_gap_orientation_invoice_zero {n P Q : ℕ}
    (cells : (Fin P × Fin Q) × Bool → Cell n) (line : Finset (Cell n))
    (gap : Fin P → ℕ)
    (horient : ∀ j, ∑ i : Fin Q,
      physicalPairLineOrientation cells (fun c => c ∈ line) (j,i) = 0) :
    (∑ p : Fin P × Fin Q, physicalPairLineOrientation cells (fun c => c ∈ line) p *
      ((gap p.1 : ℝ) / 2)) = 0 := by
  classical
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro j hj
  change (∑ i : Fin Q, physicalPairLineOrientation cells (fun c => c ∈ line) (j,i) *
    ((gap j : ℝ) / 2)) = 0
  rw [← Finset.sum_mul, horient j]
  simp

/-- The full physical line minus its explicit residual and weighted stage
reference inherits the same midpoint bound when stagewise orientations
cancel. This is conditional on that cancellation on the same square and
makes no claim about the residual or a signed diagonal reference. -/
theorem stage_gap_physical_line_zero_orientation_bound {n P Q : ℕ}
    (cells : (Fin P × Fin Q) × Bool → Cell n) (hcells : Function.Injective cells)
    (line : Finset (Cell n)) (a : Cell n ≃ Fin (n*n))
    (μ : Fin P → ℝ) (gap : Fin P → ℕ) (B : ℝ)
    (hgap : ∀ j i, entry a (cells ((j,i),true)) = entry a (cells ((j,i),false)) + gap j)
    (horient : ∀ j, ∑ i : Fin Q,
      physicalPairLineOrientation cells (fun c => c ∈ line) (j,i) = 0)
    (hbound : |∑ p : Fin P × Fin Q, physicalPairLineWeight cells (fun c => c ∈ line) p *
      ((((entry a (cells (p,false)) : ℝ) + entry a (cells (p,true))) / 2) - μ p.1)| ≤ B) :
    |(∑ c ∈ line, (entry a c : ℝ)) -
      (∑ c ∈ line \ Finset.univ.image cells, (entry a c : ℝ)) -
      (∑ p : Fin P × Fin Q, physicalPairLineWeight cells (fun c => c ∈ line) p * μ p.1)| ≤ B := by
  classical
  have hz := stage_gap_orientation_invoice_zero cells line gap horient
  have h := growth_physical_line_centered_bound cells hcells line a μ gap B hgap hbound
  simpa [hz] using h

end
end Sude
