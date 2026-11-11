import Sude.CentralConstruct

/-! Derive the post-diagonal numerical interface from explicit source bands. -/
namespace Sude
noncomputable section

/-- RF4's geometric and deletion hypotheses imply the explicit post-diagonal
interval and depletion fields. The final scalar gate remains an input. -/
theorem post_diagonal_analytic_inputs_of_bands {n bits : ℕ}
    (b : Cell n ≃ Fin (n * n)) (reserved : Finset (Cell n))
    (accounted shielded : Finset ℕ) (D : ℕ) (m σ ε w : ℝ)
    (hε : 0 ≤ ε)
    (hmean : |centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue - m| ≤
      σ * poolMaximum n)
    (hleftMargin : 1 ≤ m - (σ + ε) * poolMaximum n)
    (hrightMargin : m + (σ + ε) * poolMaximum n ≤ poolMaximum n)
    (hgap : σ + ε + w < 1 / 4)
    (hcover : (reserved ∪ unreservedDiagonalCells reserved).image (entry b) ⊆ accounted ∪ shielded)
    (haccount : accounted.card ≤ D)
    (hband : ∀ p ∈ shielded, (p : ℝ) ≤ m - (poolMaximum n : ℝ) / 4 + w * poolMaximum n ∨
      m + (poolMaximum n : ℝ) / 4 - w * poolMaximum n ≤ p)
    (hgate : (((9 * bits + 6) * n : ℕ) : ℝ) ≤
      (2 * (ε * poolMaximum n) - (1036 / 125 : ℝ) * Real.sqrt (poolMaximum n)) /
        Real.log (poolMaximum n) - D) :
    PostDiagonalAnalyticInputs b reserved bits ε D := by
  let R := reserved ∪ unreservedDiagonalCells reserved
  let μ := centralEntriesMean (actualUnusedPool b R) centralPoolValue
  let X : ℝ := poolMaximum n
  let lo := μ - ε * X
  let hi := μ + ε * X
  have hX : 0 < X := by dsimp [X]; exact_mod_cast (poolMaximum_prime n).pos
  have hrad : 0 ≤ ε * X := mul_nonneg hε hX.le
  have hbc : lo ≤ hi := by dsimp [lo, hi]; linarith
  have hmean' := abs_le.mp hmean
  have hleft : 1 ≤ lo := by dsimp [lo]; nlinarith [hmean'.1]
  have hright : hi ≤ X := by dsimp [hi]; nlinarith [hmean'.2]
  have hprotect : ∀ p ∈ shielded, p ∉ apInterval lo hi 2 1 := by
    intro p hp hpi
    have hmem := (mem_apInterval_iff lo hi 2 1 (by linarith) (by linarith) p).mp hpi
    have haway := central_window_avoids_outer_bands X m μ σ ε w p hX hmean hgap (hband p hp)
    exact haway ⟨hmem.2.1, hmem.2.2.1⟩
  have hdel := (interval_deletions_le_accounted lo hi (R.image (entry b)) accounted shielded
    hcover hprotect).trans haccount
  exact ⟨hleft, hright, hdel, hgate⟩

/-- Replace the actual remaining-cardinality denominator by the uniform
lower bound from the diagonal construction, preserving floor arithmetic. -/
theorem diagonal_mean_shift_uniform (n N : ℕ) (η : ℝ)
    (hn : 2 ≤ n) (hη : 0 ≤ η) (hN : n * n / 2 ≤ N) :
    3 * η / (N : ℝ) ≤ 6 * η / ((n * n - 1 : ℕ) : ℝ) := by
  have hn2 : 2 ≤ n * n := by nlinarith
  have hdpos : 0 < n * n - 1 := by omega
  have hdiv : n * n - 1 ≤ 2 * (n * n / 2) := by omega
  have htwo : n * n - 1 ≤ 2 * N := hdiv.trans (Nat.mul_le_mul_left 2 hN)
  have hNpos : 0 < N := by omega
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hdreal : (0 : ℝ) < (n * n - 1 : ℕ) := by exact_mod_cast hdpos
  have htwoR : ((n * n - 1 : ℕ) : ℝ) ≤ 2 * N := by exact_mod_cast htwo
  apply (div_le_div_iff₀ hNreal hdreal).2
  nlinarith [mul_nonneg hη (show 0 ≤ 2 * (N : ℝ) - ((n * n - 1 : ℕ) : ℝ) by linarith)]

/-- A pre-diagonal mean estimate and the actual diagonal mean-update bound
combine into a uniform bound relative to the original source mean. -/
theorem post_diagonal_mean_from_pair_budget {n : ℕ}
    (a b : Cell n ≃ Fin (n * n)) (reserved : Finset (Cell n))
    (η initialBound σ : ℝ) (hn : 2 ≤ n) (hη : 0 ≤ η)
    (hcount : n * n / 2 ≤ (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card)
    (hinitial : |centralEntriesMean (actualUnusedPool a reserved) centralPoolValue -
      (Lucas.poolTotal n : ℝ) / (n * n : ℕ)| ≤ initialBound)
    (hshift : |centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue -
      centralEntriesMean (actualUnusedPool a reserved) centralPoolValue| ≤
        3 * η / (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card)
    (hbudget : initialBound + 6 * η / ((n * n - 1 : ℕ) : ℝ) ≤ σ * poolMaximum n) :
    |centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue -
      (Lucas.poolTotal n : ℝ) / (n * n : ℕ)| ≤ σ * poolMaximum n := by
  have ht := abs_sub_le
    (centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue)
    (centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)
    ((Lucas.poolTotal n : ℝ) / (n * n : ℕ))
  have hc := diagonal_mean_shift_uniform n _ η hn hη hcount
  linarith

/-- Produce the construction's uniform post-diagonal interface from explicit
pair midpoint budgets, scalar margins, and a physical reservation
classification. The classification must cover the actual post-diagonal
reserved values and identify all values in the two outer bands. -/
theorem post_diagonal_inputs_from_pair_budget {n bits : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I] (a : Cell n ≃ Fin (n * n)) (reserved : Finset (Cell n))
    (pair : I × Bool → Cell n) (budget : I → ℝ) (η σ ε w : ℝ) (D : ℕ)
    (hn : 2 ≤ n) (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (hinj : Function.Injective pair)
    (hcover : (Finset.univ : Finset (I × Bool)).image pair = reserved)
    (hreserved : reserved.card < n * n)
    (hpair : ∀ i, |(entry a (pair (i, true)) : ℝ) + (entry a (pair (i, false)) : ℝ) -
      2 * ((Lucas.poolTotal n : ℝ) / (n * n : ℕ))| ≤ budget i)
    (hbudget : (∑ i, budget i) / (n * n - reserved.card : ℕ) +
      6 * η / ((n * n - 1 : ℕ) : ℝ) ≤ σ * poolMaximum n)
    (hleftMargin : 1 ≤ (Lucas.poolTotal n : ℝ) / (n * n : ℕ) - (σ + ε) * poolMaximum n)
    (hrightMargin : (Lucas.poolTotal n : ℝ) / (n * n : ℕ) + (σ + ε) * poolMaximum n ≤ poolMaximum n)
    (hgap : σ + ε + w < 1 / 4)
    (hgate : (((9 * bits + 6) * n : ℕ) : ℝ) ≤
      (2 * (ε * poolMaximum n) - (1036 / 125 : ℝ) * Real.sqrt (poolMaximum n)) /
        Real.log (poolMaximum n) - D)
    (hclassify : ∀ b : Cell n ≃ Fin (n * n),
      (∀ z ∈ reserved, entry b z = entry a z) →
      (∀ z ∈ unreservedDiagonalCells reserved,
        |(entry b z : ℝ) - (Lucas.poolTotal n : ℝ) / (n * n : ℕ)| ≤ η) →
      ∃ accounted shielded : Finset ℕ,
        (reserved ∪ unreservedDiagonalCells reserved).image (entry b) ⊆ accounted ∪ shielded ∧
        accounted.card ≤ D ∧
        (∀ p ∈ shielded, (p : ℝ) ≤ (Lucas.poolTotal n : ℝ) / (n * n : ℕ) -
          (poolMaximum n : ℝ) / 4 + w * poolMaximum n ∨
          (Lucas.poolTotal n : ℝ) / (n * n : ℕ) + (poolMaximum n : ℝ) / 4 - w * poolMaximum n ≤ p)) :
    ∀ b : Cell n ≃ Fin (n * n),
      (∀ z ∈ reserved, entry b z = entry a z) →
      (∀ z ∈ unreservedDiagonalCells reserved,
        |(entry b z : ℝ) - (Lucas.poolTotal n : ℝ) / (n * n : ℕ)| ≤ η) →
      n * n / 2 ≤ (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card →
      |centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue -
        centralEntriesMean (actualUnusedPool a reserved) centralPoolValue| ≤
          3 * η / (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card →
      PostDiagonalAnalyticInputs b reserved bits ε D := by
  intro b hfixed hcentral hcount hshift
  have hinitial := actual_unused_mean_from_reserved_pairs_source a reserved pair budget hinj hcover hreserved hpair
  have hmean := post_diagonal_mean_from_pair_budget a b reserved η
    ((∑ i, budget i) / (n * n - reserved.card : ℕ)) σ hn hη hcount hinitial hshift hbudget
  obtain ⟨accounted, shielded, hclass, haccount, hband⟩ := hclassify b hfixed hcentral
  exact post_diagonal_analytic_inputs_of_bands b reserved accounted shielded D
    ((Lucas.poolTotal n : ℝ) / (n * n : ℕ)) σ ε w hε hmean hleftMargin hrightMargin
    hgap hclass haccount hband hgate

end
end Sude
