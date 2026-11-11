import Sude.PermutedSeedMidpoints
/-! Conditional bounds for actual retained twin midpoints and their finite stage mean.
The pool mean and endpoint hypotheses are supplied explicitly. -/
namespace Sude
noncomputable section

theorem seed_midpoint_pool_bound (X μ : ℝ) (p : ℕ)
    (hX : 4 * (2^30 : ℝ) < X)
    (hlo : (243 / 500 : ℝ) * X ≤ μ)
    (hhi : μ ≤ (123 / 250 : ℝ) * X)
    (hp : p + 2 ≤ 2^30) :
    |((p : ℝ) + 1) - μ| ≤ (123 / 250 : ℝ) * X := by
  have hp' : (p : ℝ) + 2 ≤ (2^30 : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  rw [abs_le]
  constructor <;> linarith

theorem retained_seed_midpoint_pool_bound (candidates : Finset ℕ) (r P Q : ℕ)
    (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P)
    (X μ : ℝ) (hX : 4 * (2^30 : ℝ) < X)
    (hlo : (243 / 500 : ℝ) * X ≤ μ)
    (hhi : μ ≤ (123 / 250 : ℝ) * X)
    (hcap : ∀ j : Fin P, ∀ i : Fin Q,
      sortedSeedLower candidates r Q hcard (retainedSeedStageIndex r P kept hsub hkept j, i) + 2 ≤ 2^30)
    (j : Fin P) (i : Fin Q) :
    |retainedStageMidpoint candidates r P Q 2 hcard kept hsub hkept j i - μ| ≤
      (123 / 250 : ℝ) * X := by
  let x := (retainedSeedStageIndex r P kept hsub hkept j, i)
  have hp := hcap j i
  have h := seed_midpoint_pool_bound X μ (sortedSeedLower candidates r Q hcard x) hX hlo hhi hp
  have hm : retainedStageMidpoint candidates r P Q 2 hcard kept hsub hkept j i =
      (sortedSeedLower candidates r Q hcard x : ℝ) + 1 := by
    simp [retainedStageMidpoint, sortedSeedMidpoint, sortedSeedEndpoint, pairEndpoint, x]
    ring
  rw [hm]
  exact h
/-- The complete retained stage's actual finite midpoint mean obeys the same bound. -/
theorem retained_seed_stage_mean_pool_bound (candidates : Finset ℕ) (r P Q : ℕ)
    (hcard : candidates.card = r * Q) (kept : Finset ℕ)
    (hsub : kept ⊆ Finset.range r) (hkept : kept.card = P) (hQ : 0 < Q)
    (X μ : ℝ) (hX : 4 * (2^30 : ℝ) < X)
    (hlo : (243 / 500 : ℝ) * X ≤ μ)
    (hhi : μ ≤ (123 / 250 : ℝ) * X)
    (hcap : ∀ j : Fin P, ∀ i : Fin Q,
      sortedSeedLower candidates r Q hcard (retainedSeedStageIndex r P kept hsub hkept j, i) + 2 ≤ 2^30) (j : Fin P) :
    |(∑ i : Fin Q, retainedStageMidpoint candidates r P Q 2 hcard kept hsub hkept j i) /
        (Q : ℝ) - μ| ≤ (123 / 250 : ℝ) * X := by
  let v := retainedStageMidpoint candidates r P Q 2 hcard kept hsub hkept j
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have ht : (∑ i : Fin Q, |v i - μ|) ≤ (Q : ℝ) * ((123 / 250 : ℝ) * X) := by
    calc
      _ ≤ ∑ _i : Fin Q, ((123 / 250 : ℝ) * X) := by
        apply Finset.sum_le_sum
        intro i _
        exact retained_seed_midpoint_pool_bound candidates r P Q hcard kept hsub hkept X μ hX hlo hhi hcap j i
      _ = _ := by simp
  have hs := (Finset.abs_sum_le_sum_abs (fun i : Fin Q => v i - μ) Finset.univ).trans ht
  have heq : (∑ i : Fin Q, v i) / (Q : ℝ) - μ = (∑ i : Fin Q, (v i - μ)) / (Q : ℝ) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    field_simp
  change |(∑ i : Fin Q, v i) / (Q : ℝ) - μ| ≤ _
  rw [heq, abs_div, abs_of_pos hQr, div_le_iff₀ hQr]
  nlinarith

end
end Sude
