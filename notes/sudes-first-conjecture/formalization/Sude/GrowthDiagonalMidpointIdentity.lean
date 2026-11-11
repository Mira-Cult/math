import Sude.PhysicalPairLineSum

/-! Exact line contribution of labelled stage pairs with a designated
12-slot indicator and low-endpoint orientation. -/
namespace Sude
noncomputable section

/-- With twelve low-side incidences per stage and stage-constant gaps, the
actual contribution of the supplied pair-cell image is the sum of the
selected physical midpoints minus six times the sum of the stage gaps.
The ambient line cells outside that image remain a separate obligation. -/
theorem growth_diagonal_midpoint_identity {n P Q : ℕ}
    (cells : (Fin P × Fin Q) × Bool → Cell n) (hcells : Function.Injective cells)
    (line : Cell n → Prop) [DecidablePred line] (a : Cell n ≃ Fin (n*n))
    (S : Fin P → Finset (Fin Q)) (gap : Fin P → ℕ)
    (hcard : ∀ j, (S j).card = 12)
    (hweight : ∀ j i, physicalPairLineWeight cells line (j,i) = if i ∈ S j then 1 else 0)
    (horient : ∀ j i, physicalPairLineOrientation cells line (j,i) =
      -(physicalPairLineWeight cells line (j,i)))
    (hgap : ∀ j i, entry a (cells ((j,i),true)) = entry a (cells ((j,i),false)) + gap j) :
    (∑ c ∈ (Finset.univ.image cells).filter line, (entry a c : ℝ)) =
      (∑ j, ∑ i ∈ S j, (((entry a (cells ((j,i),false)) : ℝ) +
        entry a (cells ((j,i),true))) / 2)) - 6 * ∑ j, (gap j : ℝ) := by
  classical
  rw [physicalPair_line_sum_midpoint cells hcells line a, Fintype.sum_prod_type]
  have hstage : ∀ j,
      (∑ i, (physicalPairLineWeight cells line (j,i) *
        (((entry a (cells ((j,i),false)) : ℝ) + entry a (cells ((j,i),true))) / 2) +
        physicalPairLineOrientation cells line (j,i) *
        (((entry a (cells ((j,i),true)) : ℝ) - entry a (cells ((j,i),false))) / 2))) =
      (∑ i ∈ S j, (((entry a (cells ((j,i),false)) : ℝ) +
        entry a (cells ((j,i),true))) / 2)) - 6 * (gap j : ℝ) := by
    intro j
    have hg (i : Fin Q) : ((entry a (cells ((j,i),true)) : ℝ) -
        entry a (cells ((j,i),false))) = gap j := by
      have h : (entry a (cells ((j,i),true)) : ℝ) =
          (entry a (cells ((j,i),false)) : ℝ) + (gap j : ℝ) := by exact_mod_cast hgap j i
      linarith
    simp_rw [horient, hweight, hg]
    simp only [neg_ite, neg_zero, ite_mul, one_mul, zero_mul, neg_mul]
    rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const, hcard, nsmul_eq_mul]
    ring
  simp_rw [hstage]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]

end
end Sude
