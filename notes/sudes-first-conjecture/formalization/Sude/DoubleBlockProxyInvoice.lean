import Sude.DoubleBlockLogSelection

/-! Algebraic bridge from supplied physical pair-weight invoices to the
double-block probability proxy. No geometric invoice is asserted here. -/
namespace Sude
noncomputable section

/-- The stage-permutation plus internal-swap proxy is exactly one half of
the width-squared weighted invoice for the two physical pair slots. -/
theorem double_block_combined_proxy_eq_pair_invoice {n P B : ℕ}
    (cells : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (line : Cell n → Prop) (lo hi : Fin P → ℝ) (horder : ∀ j, lo j ≤ hi j) :
    doubleBlockCombinedProxy cells line lo hi =
      (∑ j, (hi j - lo j) ^ 2 * ∑ b, ∑ p : Fin 2,
        (physicalPairLineWeight cells line (j, b, p)) ^ 2) / 2 := by
  classical
  have hnonneg : ∀ j b, b ∈ (Finset.univ : Finset (Fin B)) →
      0 ≤ doubleBlockLineWeight cells line j b := by
    intro j b _
    unfold doubleBlockLineWeight physicalPairLineWeight
    split_ifs <;> norm_num
  unfold doubleBlockCombinedProxy
  rw [stageWeightedProxy_real (fun _ => Finset.univ) _ lo hi horder hnonneg]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  rw [Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  unfold doubleBlockLineWeight
  ring

/-- A supplied upper bound on the weighted pair invoice pays the proxy gate
used by the finite simultaneous double-block allocation theorem. -/
theorem double_block_proxy_le_of_pair_invoice {n P B : ℕ}
    (cells : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (line : Cell n → Prop) (lo hi : Fin P → ℝ) (V : ℝ)
    (horder : ∀ j, lo j ≤ hi j)
    (hinvoice : 2 * (∑ j, (hi j - lo j) ^ 2 * ∑ b, ∑ p : Fin 2,
      (physicalPairLineWeight cells line (j, b, p)) ^ 2) ≤ V) :
    doubleBlockCombinedProxy cells line lo hi ≤ V / 4 := by
  rw [double_block_combined_proxy_eq_pair_invoice cells line lo hi horder]
  linarith

/-- Uniform nonnegative width and squared-incidence bounds yield a
nonnegative proxy invoice. Positivity, when needed, remains separate. -/
theorem double_block_proxy_uniform_pair_invoice {n P B : ℕ}
    (cells : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (line : Cell n → Prop) (lo hi : Fin P → ℝ) (hlu : ∀ j, lo j ≤ hi j)
    (C M : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hwidth : ∀ j, hi j - lo j ≤ C)
    (hmass : (∑ j, ∑ b, ∑ p : Fin 2, (physicalPairLineWeight cells line (j,b,p)) ^ 2) ≤ M) :
    0 ≤ 2 * C ^ 2 * M ∧ doubleBlockCombinedProxy cells line lo hi ≤ (2 * C ^ 2 * M) / 4 := by
  classical
  have hwidthSq (j : Fin P) : (hi j - lo j)^2 ≤ C^2 := by
    nlinarith [hlu j, hwidth j, hC, sq_nonneg (C - (hi j - lo j))]
  have hpoint : ∀ j : Fin P, 0 ≤ ∑ b, ∑ p : Fin 2, (physicalPairLineWeight cells line (j,b,p)) ^ 2 := by
    intro j
    exact Finset.sum_nonneg (fun b _ => Finset.sum_nonneg (fun p _ => sq_nonneg _))
  have hw : (∑ j, (hi j - lo j)^2 * ∑ b, ∑ p : Fin 2,
        (physicalPairLineWeight cells line (j,b,p))^2) ≤ C^2 * M := by
    calc
      _ ≤ ∑ j, C^2 * ∑ b, ∑ p : Fin 2, (physicalPairLineWeight cells line (j,b,p))^2 := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right (hwidthSq j) (hpoint j)
      _ = C^2 * (∑ j, ∑ b, ∑ p : Fin 2, (physicalPairLineWeight cells line (j,b,p))^2) := by
        rw [Finset.mul_sum]
      _ ≤ C^2 * M := mul_le_mul_of_nonneg_left hmass (sq_nonneg C)
  constructor
  · positivity
  · rw [double_block_combined_proxy_eq_pair_invoice cells line lo hi hlu]
    linarith


end
end Sude
