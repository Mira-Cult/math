import Sude.FWPermutationExceptions
import Sude.FWEntropyIntervalGate

/-! Fixed-cut FW hypergeometric law and entropy estimates. These results do
not sum over all cuts or assert the existence of an expander. -/
namespace Sude
noncomputable section
open scoped BigOperators

/-- The FW bad-tuple hypergeometric numerator for a cut of size `s`. -/
def fwPermutationCutWeight (n s : ℕ) : ℕ :=
  ∑ j ∈ (Finset.univ : Finset (Fin 3 → Fin (s + 1))).filter
      (fun j => 1000 * (∑ i, (j i).val) < 519 * min s (n - s)),
    ∏ i, (Nat.choose s (j i).val * Nat.choose (n - s) (j i).val)

/-- The exact FW fixed-cut probability count, indexed by cut size. -/
def fwPermutationFixedCutCount (n s : ℕ) : ℕ :=
  (fwPermutationFixedCutBad (permutationCanonicalCut n s)).card

/-- The exact FW fixed-cut hypergeometric count. -/
theorem fwPermutationFixedCutBad_scaled_card {n : ℕ} (S : Finset (Fin n)) :
    (Nat.choose n S.card)^3 * (fwPermutationFixedCutBad S).card =
      (n.factorial)^3 * fwPermutationCutWeight n S.card := by
  classical
  unfold fwPermutationCutWeight
  change (Nat.choose n S.card)^3 * (fwPermutationFixedCutBad S).card =
      (n.factorial)^3 * ∑ j ∈ fwPermutationBadCountTuples S,
        ∏ i, (Nat.choose S.card (j i).val * Nat.choose (n - S.card) (j i).val)
  rw [fwPermutationFixedCutBad_card_partition, Finset.mul_sum]
  calc
    _ = ∑ j ∈ fwPermutationBadCountTuples S,
        (n.factorial)^3 * ∏ i, (Nat.choose S.card (j i).val * Nat.choose (n - S.card) (j i).val) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact permutationCountTuple_hypergeometric S (fun i => (j i).val)
        (fun i => Nat.le_of_lt_succ (j i).isLt)
    _ = _ := by rw [Finset.mul_sum]

/-- The exact FW count depends only on the cut's cardinality. -/
theorem fwPermutationFixedCutBad_card_eq {n : ℕ} (S T : Finset (Fin n))
    (hcard : S.card = T.card) :
    (fwPermutationFixedCutBad S).card = (fwPermutationFixedCutBad T).card := by
  have hs := fwPermutationFixedCutBad_scaled_card S
  have ht := fwPermutationFixedCutBad_scaled_card T
  rw [hcard] at hs
  have hchoose : 0 < Nat.choose n T.card := Nat.choose_pos (by simpa using Finset.card_le_univ T)
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hchoose 3) (hs.trans ht.symm)

theorem fwPermutationFixedCutCount_spec {n : ℕ} (S : Finset (Fin n)) :
    (fwPermutationFixedCutBad S).card = fwPermutationFixedCutCount n S.card := by
  unfold fwPermutationFixedCutCount
  apply fwPermutationFixedCutBad_card_eq
  exact (permutationCanonicalCut_card (by simpa using Finset.card_le_univ S)).symm

theorem fwPermutationFixedCutCount_scaled {n s : ℕ} (hs : s ≤ n) :
    (Nat.choose n s)^3 * fwPermutationFixedCutCount n s =
      (n.factorial)^3 * fwPermutationCutWeight n s := by
  have h := fwPermutationFixedCutBad_scaled_card (permutationCanonicalCut n s)
  simpa [fwPermutationFixedCutCount, permutationCanonicalCut_card hs] using h

/-- FW's exact three-count entropy bound for a smaller-side cut. -/
theorem fw_entropy_tuple_bound {n s : ℕ} (hs : 0 < s) (hhalf : 2 * s ≤ n)
    (j : Fin 3 → Fin (s + 1)) (hbad : 1000 * (∑ i, (j i).val) < 519 * s) :
    (∑ i : Fin 3, ((s : ℝ) * Real.binEntropy ((j i).val / (s : ℝ)) +
      ((n - s : ℕ) : ℝ) * Real.binEntropy ((j i).val / ((n - s : ℕ) : ℝ)))) ≤
      3 * ((s : ℝ) * Real.binEntropy ((173 : ℝ) / 1000) +
        ((n - s : ℕ) : ℝ) * Real.binEntropy (((173 : ℝ) / 1000) * s / ((n - s : ℕ) : ℝ))) := by
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs
  have hns : s ≤ n - s := by omega
  have hnspos : (0 : ℝ) < (n - s : ℕ) := by exact_mod_cast (show 0 < n - s by omega)
  have hsle : (s : ℝ) ≤ (n - s : ℕ) := by exact_mod_cast hns
  have hjle (i : Fin 3) : ((j i).val : ℝ) ≤ s := by exact_mod_cast Nat.le_of_lt_succ (j i).isLt
  have hbadR : (1000 : ℝ) * (∑ i, ((j i).val : ℝ)) < 519 * s := by
    exact_mod_cast hbad
  have hbound1 : (∑ i, ((j i).val : ℝ) / s) ≤ 3 * ((173 : ℝ) / 1000) := by
    rw [← Finset.sum_div]
    apply (div_le_iff₀ hspos).2
    linarith
  have hbound2 : (∑ i, ((j i).val : ℝ) / ((n - s : ℕ) : ℝ)) ≤
      3 * (((173 : ℝ) / 1000) * s / ((n - s : ℕ) : ℝ)) := by
    rw [← Finset.sum_div]
    apply (div_le_iff₀ hnspos).2
    have hcancel : (3 * (((173 : ℝ) / 1000) * s / ((n - s : ℕ) : ℝ))) *
        ((n - s : ℕ) : ℝ) = 3 * ((173 : ℝ) / 1000) * s := by
      field_simp
    rw [hcancel]
    linarith
  have hx1 : ∀ i, 0 ≤ ((j i).val : ℝ) / s ∧ ((j i).val : ℝ) / s ≤ 1 := by
    intro i
    exact ⟨by positivity, (div_le_one hspos).2 (hjle i)⟩
  have hx2 : ∀ i, 0 ≤ ((j i).val : ℝ) / ((n - s : ℕ) : ℝ) ∧
      ((j i).val : ℝ) / ((n - s : ℕ) : ℝ) ≤ 1 := by
    intro i
    exact ⟨by positivity, (div_le_one hnspos).2 ((hjle i).trans hsle)⟩
  have hb0 : 0 ≤ ((173 : ℝ) / 1000) * s / ((n - s : ℕ) : ℝ) := by positivity
  have hb1 : ((173 : ℝ) / 1000) * s / ((n - s : ℕ) : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ hnspos).2
    nlinarith
  have h1 := entropy_sum_three_le _ (173 / 1000) hx1 (by norm_num) (by norm_num) hbound1
  have h2 := entropy_sum_three_le _ (((173 : ℝ) / 1000) * s / ((n - s : ℕ) : ℝ))
    hx2 hb0 hb1 hbound2
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  nlinarith

/-- Every bad three-count tuple has its hypergeometric numerator bounded by
the source's common entropy exponential. -/
theorem fw_tuple_choose_entropy_bound {n s : ℕ} (hs : 0 < s) (hhalf : 2 * s ≤ n)
    (j : Fin 3 → Fin (s + 1)) (hbad : 1000 * (∑ i, (j i).val) < 519 * s) :
    (∏ i, ((s.choose (j i).val : ℕ) : ℝ) * (((n - s).choose (j i).val : ℕ) : ℝ)) ≤
      Real.exp (3 * ((s : ℝ) * Real.binEntropy ((173 : ℝ) / 1000) +
        ((n - s : ℕ) : ℝ) * Real.binEntropy (((173 : ℝ) / 1000) * s / ((n - s : ℕ) : ℝ)))) := by
  have hns : s ≤ n - s := by omega
  calc
    _ ≤ ∏ i : Fin 3, (Real.exp ((s : ℝ) * Real.binEntropy ((j i).val / (s : ℝ))) *
        Real.exp (((n - s : ℕ) : ℝ) * Real.binEntropy ((j i).val / ((n - s : ℕ) : ℝ)))) := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        have hj : (j i).val ≤ s := Nat.le_of_lt_succ (j i).isLt
        exact mul_le_mul (binomial_choose_le_exp_entropy_all hj)
          (binomial_choose_le_exp_entropy_all (hj.trans hns)) (by positivity) (by positivity)
    _ = Real.exp (∑ i : Fin 3, ((s : ℝ) * Real.binEntropy ((j i).val / (s : ℝ)) +
        ((n - s : ℕ) : ℝ) * Real.binEntropy ((j i).val / ((n - s : ℕ) : ℝ)))) := by
      simp_rw [← Real.exp_add]
      rw [Real.exp_sum]
    _ ≤ _ := (Real.exp_le_exp).2 (fw_entropy_tuple_bound hs hhalf j hbad)

/-- The complete fixed-cut hypergeometric numerator is bounded by the
number of possible count triples times the common entropy exponential. -/
theorem fw_cutWeight_entropy_bound {n s : ℕ} (hs : 0 < s) (hhalf : 2 * s ≤ n) :
    (fwPermutationCutWeight n s : ℝ) ≤ ((s + 1 : ℕ) : ℝ)^3 *
      Real.exp (3 * ((s : ℝ) * Real.binEntropy ((173 : ℝ) / 1000) +
        ((n - s : ℕ) : ℝ) * Real.binEntropy (((173 : ℝ) / 1000) * s / ((n - s : ℕ) : ℝ)))) := by
  classical
  let A : Finset (Fin 3 → Fin (s + 1)) := Finset.univ.filter
    (fun j => 1000 * (∑ i, (j i).val) < 519 * min s (n - s))
  let C : ℝ := Real.exp (3 * ((s : ℝ) * Real.binEntropy ((173 : ℝ) / 1000) +
        ((n - s : ℕ) : ℝ) * Real.binEntropy (((173 : ℝ) / 1000) * s / ((n - s : ℕ) : ℝ))))
  have hmin : min s (n - s) = s := Nat.min_eq_left (by omega)
  have hterm (j : Fin 3 → Fin (s + 1)) (hj : j ∈ A) :
      (∏ i, ((s.choose (j i).val : ℕ) : ℝ) * (((n - s).choose (j i).val : ℕ) : ℝ)) ≤ C := by
    have hbad := (Finset.mem_filter.mp hj).2
    rw [hmin] at hbad
    exact fw_tuple_choose_entropy_bound hs hhalf j hbad
  have hsum := Finset.sum_le_card_nsmul A
    (fun j => ∏ i, ((s.choose (j i).val : ℕ) : ℝ) * (((n - s).choose (j i).val : ℕ) : ℝ)) C hterm
  have hcard : A.card ≤ (s + 1)^3 := by
    have h := Finset.card_le_univ A
    simpa [Fintype.card_fun] using h
  have hcardR : (A.card : ℝ) ≤ ((s + 1 : ℕ) : ℝ)^3 := by exact_mod_cast hcard
  have hsum' : (∑ j ∈ A, ∏ i, ((s.choose (j i).val : ℕ) : ℝ) *
      (((n - s).choose (j i).val : ℕ) : ℝ)) ≤ (A.card : ℝ) * C := by
    simpa using hsum
  have hfinal := hsum'.trans (mul_le_mul_of_nonneg_right hcardR (Real.exp_nonneg _))
  simpa [fwPermutationCutWeight, A, C] using hfinal

/-- Scaling the cut entropy by the number of vertices gives exactly the
source numerator-minus-denominator entropy expression. -/
theorem fw_cut_entropy_scaling {n s : ℕ} (hs : 0 < s) (hhalf : 2 * s ≤ n) :
    3 * ((s : ℝ) * Real.binEntropy ((173 : ℝ) / 1000) +
      ((n - s : ℕ) : ℝ) * Real.binEntropy (((173 : ℝ) / 1000) * s / ((n - s : ℕ) : ℝ))) -
      2 * (n : ℝ) * Real.binEntropy ((s : ℝ) / n) =
        (n : ℝ) * fwCutEntropy ((s : ℝ) / n) := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hns : ((n - s : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show n - s ≠ 0 by omega)
  have hsub : ((n - s : ℕ) : ℝ) = (n : ℝ) - s := Nat.cast_sub (by omega)
  have hcomp : 1 - (s : ℝ) / n = ((n - s : ℕ) : ℝ) / n := by
    rw [hsub]
    field_simp
  have hratio : ((173 : ℝ) / 1000) * ((s : ℝ) / n) / (1 - (s : ℝ) / n) =
      ((173 : ℝ) / 1000) * s / ((n - s : ℕ) : ℝ) := by
    rw [hcomp]
    field_simp
  unfold fwCutEntropy
  rw [hratio, hcomp]
  field_simp

/-- The large-cut union-bound summand, normalized by the uniform triple
sample-space cardinality, is bounded by the source entropy expression. -/
theorem fw_fixedCut_large_entropy_bound {n s : ℕ} (hs : 0 < s) (hhalf : 2 * s ≤ n) :
    ((Nat.choose n s : ℝ) * (fwPermutationFixedCutCount n s : ℝ)) / (n.factorial : ℝ)^3 ≤
      ((n + 1 : ℕ) : ℝ)^2 * ((s + 1 : ℕ) : ℝ)^3 *
        Real.exp ((n : ℝ) * fwCutEntropy ((s : ℝ) / n)) := by
  let C : ℝ := Nat.choose n s
  let F : ℝ := n.factorial
  let W : ℝ := fwPermutationCutWeight n s
  let H : ℝ := (n : ℝ) * Real.binEntropy ((s : ℝ) / n)
  let E : ℝ := 3 * ((s : ℝ) * Real.binEntropy ((173 : ℝ) / 1000) +
    ((n - s : ℕ) : ℝ) * Real.binEntropy (((173 : ℝ) / 1000) * s / ((n - s : ℕ) : ℝ)))
  have hC : 0 < C := by dsimp [C]; exact_mod_cast Nat.choose_pos (by omega : s ≤ n)
  have hF : 0 < F := by dsimp [F]; exact_mod_cast Nat.factorial_pos n
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hchoose := binomial_exp_entropy_le_succ_mul_choose_all (show s ≤ n by omega)
  have hdiv : 1 / C ≤ ((n + 1 : ℕ) : ℝ) / Real.exp H := by
    apply (div_le_div_iff₀ hC (Real.exp_pos H)).2
    simpa [C, H] using hchoose
  have hsquare := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 / C by positivity) hdiv 2
  have hw : W ≤ ((s + 1 : ℕ) : ℝ)^3 * Real.exp E := by
    simpa [W, E] using fw_cutWeight_entropy_bound hs hhalf
  have heq : C^3 * (fwPermutationFixedCutCount n s : ℝ) = F^3 * W := by
    dsimp [C, F, W]
    exact_mod_cast fwPermutationFixedCutCount_scaled (show s ≤ n by omega)
  have hnorm : C * (fwPermutationFixedCutCount n s : ℝ) / F^3 = W * (1 / C)^2 := by
    have hCne := ne_of_gt hC
    have hFne := ne_of_gt hF
    field_simp
    nlinarith [heq]
  change C * (fwPermutationFixedCutCount n s : ℝ) / F^3 ≤ _
  rw [hnorm]
  calc
    _ ≤ (((s + 1 : ℕ) : ℝ)^3 * Real.exp E) *
          (((n + 1 : ℕ) : ℝ) / Real.exp H)^2 := by
      exact mul_le_mul hw hsquare (sq_nonneg _) (by positivity)
    _ = ((n + 1 : ℕ) : ℝ)^2 * ((s + 1 : ℕ) : ℝ)^3 * Real.exp (E - 2 * H) := by
      rw [Real.exp_sub]
      have hpow : Real.exp (2 * H) = Real.exp H ^ 2 := by
        simpa using Real.exp_nat_mul H 2
      rw [hpow]
      field_simp
    _ = _ := by
      have hscale : E - 2 * H = (n : ℝ) * fwCutEntropy ((s : ℝ) / n) := by
        dsimp [E, H]
        nlinarith [fw_cut_entropy_scaling hs hhalf]
      rw [hscale]

/-- On the actual large-cut interval each normalized cut-size summand has
uniform exponential decay. -/
theorem fw_large_cut_summand_bound {n s : ℕ} (hs : 0 < s) (hhalf : 2 * s ≤ n)
    (hlarge : n ≤ 256 * s) :
    ((Nat.choose n s : ℝ) * (fwPermutationFixedCutCount n s : ℝ)) / (n.factorial : ℝ)^3 ≤
      ((n + 1 : ℕ) : ℝ)^5 * Real.exp (-(n : ℝ) / 250) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hhalfR : (2 : ℝ) * s ≤ n := by exact_mod_cast hhalf
  have hlargeR : (n : ℝ) ≤ 256 * s := by exact_mod_cast hlarge
  have ht0 : (1 : ℝ) / 256 ≤ (s : ℝ) / n := by
    apply (le_div_iff₀ hn).2
    linarith
  have ht1 : (s : ℝ) / n ≤ 1 / 2 := by
    apply (div_le_iff₀ hn).2
    linarith
  have hent := fw_entropy_interval_gate ht0 ht1
  have hexp : Real.exp ((n : ℝ) * fwCutEntropy ((s : ℝ) / n)) ≤
      Real.exp (-(n : ℝ) / 250) := by
    apply (Real.exp_le_exp).2
    nlinarith
  have hsp : ((s + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show s + 1 ≤ n + 1 by omega)
  have hpowers : ((s + 1 : ℕ) : ℝ)^3 ≤ ((n + 1 : ℕ) : ℝ)^3 :=
    pow_le_pow_left₀ (by positivity) hsp 3
  calc
    _ ≤ ((n + 1 : ℕ) : ℝ)^2 * ((s + 1 : ℕ) : ℝ)^3 *
        Real.exp ((n : ℝ) * fwCutEntropy ((s : ℝ) / n)) :=
      fw_fixedCut_large_entropy_bound hs hhalf
    _ ≤ ((n + 1 : ℕ) : ℝ)^2 * ((n + 1 : ℕ) : ℝ)^3 * Real.exp (-(n : ℝ) / 250) := by
      gcongr
    _ = _ := by ring

/-- The size-weighted normalized failure count for an actual large cut.
The factor `choose n |S|` is retained for the later union over all cuts. -/
theorem fw_actual_fixedCut_large_bound {n : ℕ} (S : Finset (Fin n))
    (hs : 0 < S.card) (hhalf : 2 * S.card ≤ n) (hlarge : n ≤ 256 * S.card) :
    ((Nat.choose n S.card : ℝ) * (fwPermutationFixedCutBad S).card) /
        (n.factorial : ℝ)^3 ≤
      ((n + 1 : ℕ) : ℝ)^5 * Real.exp (-(n : ℝ) / 250) := by
  rw [fwPermutationFixedCutCount_spec S]
  exact fw_large_cut_summand_bound hs hhalf hlarge

end
end Sude
