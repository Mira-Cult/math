import Sude.FWPermutationExceptions

/-! FW's fixed-cut exception union, with the binomial sum and entropy
exponential exposed. No numerical decay or expander conclusion is asserted. -/
namespace Sude
noncomputable section
open scoped BigOperators

/-- FW's exact exception budget has at most this lower binomial sum of
labelled patterns. The bound retains the `3|S| - q` containment exponent. -/
theorem fwPermutationFixedCutBad_exception_sum_bound {n : ℕ} (S : Finset (Fin n))
    (hn : 0 < n) (hs : 0 < S.card) :
    ((fwPermutationFixedCutBad S).card : ℝ) / (n.factorial : ℝ)^3 ≤
      (∑ k ∈ Finset.range (519 * S.card / 1000 + 1),
        ((3 * S.card).choose k : ℝ)) *
          ((S.card : ℝ) / n)^(3 * S.card - (519 * S.card / 1000)) := by
  classical
  let q := 519 * S.card / 1000
  let A := permutationExceptionPatterns S q
  let B : ℝ := ((S.card : ℝ) / n)^(3 * S.card - q)
  have hq : q ≤ 3 * S.card := by dsimp [q]; omega
  have hF : 0 < (n.factorial : ℝ)^3 := pow_pos (by exact_mod_cast Nat.factorial_pos n) _
  have hunion := fwPermutationFixedCutBad_exception_union_bound S
  have hunionR : ((fwPermutationFixedCutBad S).card : ℝ) ≤
      ∑ E ∈ A, ((permutationFamilyContainmentEvent (permutationKeptInputs S E) S).card : ℝ) := by
    exact_mod_cast hunion
  have hsum : (∑ E ∈ A, ((permutationFamilyContainmentEvent (permutationKeptInputs S E) S).card : ℝ) /
      (n.factorial : ℝ)^3) ≤ (A.card : ℝ) * B := by
    have h := Finset.sum_le_card_nsmul A
      (fun E => ((permutationFamilyContainmentEvent (permutationKeptInputs S E) S).card : ℝ) /
        (n.factorial : ℝ)^3) B (by
          intro E hE
          exact permutationException_containment_bound S hn hs hq E hE)
    simpa using h
  have hnorm : ((fwPermutationFixedCutBad S).card : ℝ) / (n.factorial : ℝ)^3 ≤ (A.card : ℝ) * B := by
    calc
      _ ≤ (∑ E ∈ A, ((permutationFamilyContainmentEvent (permutationKeptInputs S E) S).card : ℝ)) /
          (n.factorial : ℝ)^3 := div_le_div_of_nonneg_right hunionR hF.le
      _ = ∑ E ∈ A, ((permutationFamilyContainmentEvent (permutationKeptInputs S E) S).card : ℝ) /
          (n.factorial : ℝ)^3 := Finset.sum_div ..
      _ ≤ _ := hsum
  have hcount : (A.card : ℝ) = ∑ k ∈ Finset.range (q + 1),
      ((3 * S.card).choose k : ℝ) := by
    rw [show A.card = ∑ k ∈ Finset.range (q + 1), (3 * S.card).choose k by
      exact permutationExceptionPatterns_card S q]
    push_cast
    rfl
  simpa [q, B, hcount] using hnorm

/-- Generic entropy bound specialized to FW's exact rational threshold. -/
theorem fw_exception_binomial_bound (s r : ℕ) (hr : 1000 * r ≤ 519 * s) :
    (∑ k ∈ Finset.range (r + 1), ((3 * s).choose k : ℝ)) ≤
      Real.exp ((3 * s : ℕ) * Real.binEntropy ((173 : ℝ) / 1000)) := by
  apply binomial_lower_tail_le_exp_entropy (3 * s) r (173 / 1000)
    (by norm_num) (by norm_num) (by omega)
  have hreal : (1000 : ℝ) * r ≤ 519 * s := by exact_mod_cast hr
  push_cast
  linarith

/-- FW fixed-cut bound with the source entropy factor left explicit. -/
theorem fwPermutationFixedCutBad_exception_entropy_bound {n : ℕ} (S : Finset (Fin n))
    (hn : 0 < n) (hs : 0 < S.card) :
    ((fwPermutationFixedCutBad S).card : ℝ) / (n.factorial : ℝ)^3 ≤
      Real.exp ((3 * S.card : ℕ) * Real.binEntropy ((173 : ℝ) / 1000)) *
        ((S.card : ℝ) / n)^(3 * S.card - (519 * S.card / 1000)) := by
  have hq : 1000 * (519 * S.card / 1000) ≤ 519 * S.card := by omega
  have hbin := fw_exception_binomial_bound S.card (519 * S.card / 1000) hq
  exact (fwPermutationFixedCutBad_exception_sum_bound S hn hs).trans
    (mul_le_mul_of_nonneg_right hbin (by positivity))

end
end Sude
