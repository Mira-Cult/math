import Sude.LineResidualDecomposition

/-! Exact physical-entry bookkeeping for stage-dependent growth gaps.
No gap orientation, residual sum or complete line is bounded here. -/
namespace Sude
noncomputable section

/-- A complete physical line splits into its residual cells, its selected
stage-mean reference, a centered midpoint contribution and the exact signed
half-gap orientation invoice. Each stage may have a different common gap. -/
theorem growth_physical_line_centered_identity {n P Q : ℕ}
    (cells : (Fin P × Fin Q) × Bool → Cell n) (hcells : Function.Injective cells)
    (line : Finset (Cell n)) (a : Cell n ≃ Fin (n*n))
    (μ : Fin P → ℝ) (gap : Fin P → ℕ)
    (hgap : ∀ j i, entry a (cells ((j,i),true)) = entry a (cells ((j,i),false)) + gap j) :
    (∑ c ∈ line, (entry a c : ℝ)) -
      (∑ c ∈ line \ Finset.univ.image cells, (entry a c : ℝ)) -
      (∑ p : Fin P × Fin Q, physicalPairLineWeight cells (fun c => c ∈ line) p * μ p.1) -
      (∑ p : Fin P × Fin Q, physicalPairLineOrientation cells (fun c => c ∈ line) p * (gap p.1 / 2 : ℝ)) =
    ∑ p : Fin P × Fin Q, physicalPairLineWeight cells (fun c => c ∈ line) p *
      ((((entry a (cells (p,false)) : ℝ) + entry a (cells (p,true))) / 2) - μ p.1) := by
  classical
  have hg (p : Fin P × Fin Q) : (entry a (cells (p,true)) : ℝ) - entry a (cells (p,false)) = gap p.1 := by
    have h : (entry a (cells (p,true)) : ℝ) = (entry a (cells (p,false)) : ℝ) + (gap p.1 : ℝ) := by
      exact_mod_cast hgap p.1 p.2
    linarith
  rw [fullLine_sum_pair_and_residual cells hcells line a]
  simp_rw [hg]
  simp only [Finset.sum_add_distrib, mul_sub, Finset.sum_sub_distrib]
  ring

/-- Any bound for that same-square centered midpoint contribution transfers
without loss, retaining the complete residual sum and signed stage-gap
invoice as explicit terms. It does not bound either term. -/
theorem growth_physical_line_centered_bound {n P Q : ℕ}
    (cells : (Fin P × Fin Q) × Bool → Cell n) (hcells : Function.Injective cells)
    (line : Finset (Cell n)) (a : Cell n ≃ Fin (n*n))
    (μ : Fin P → ℝ) (gap : Fin P → ℕ) (B : ℝ)
    (hgap : ∀ j i, entry a (cells ((j,i),true)) = entry a (cells ((j,i),false)) + gap j)
    (hbound : |∑ p : Fin P × Fin Q, physicalPairLineWeight cells (fun c => c ∈ line) p *
      ((((entry a (cells (p,false)) : ℝ) + entry a (cells (p,true))) / 2) - μ p.1)| ≤ B) :
    |(∑ c ∈ line, (entry a c : ℝ)) -
      (∑ c ∈ line \ Finset.univ.image cells, (entry a c : ℝ)) -
      (∑ p : Fin P × Fin Q, physicalPairLineWeight cells (fun c => c ∈ line) p * μ p.1) -
      (∑ p : Fin P × Fin Q, physicalPairLineOrientation cells (fun c => c ∈ line) p * (gap p.1 / 2 : ℝ))| ≤ B := by
  rw [growth_physical_line_centered_identity cells hcells line a μ gap hgap]
  exact hbound

end
end Sude
