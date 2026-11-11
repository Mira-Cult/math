import Sude.BinomialMode
import Sude.PermutationCutUnion

/-! Jensen maximization for the three outgoing permutation counts. -/
namespace Sude
noncomputable section
open scoped BigOperators

/-- Three binary entropies are bounded by the entropy at any upper bound
for their average in `[0, 1/2]`. Individual inputs may exceed `1/2`. -/
theorem entropy_sum_three_le (x : Fin 3 → ℝ) (a : ℝ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    (hsum : (∑ i, x i) ≤ 3 * a) :
    (∑ i, Real.binEntropy (x i)) ≤ 3 * Real.binEntropy a := by
  have hj := Real.strictConcave_binEntropy.concaveOn.le_map_sum
    (t := Finset.univ) (w := fun _ : Fin 3 => (1 : ℝ) / 3) (p := x)
    (by intro i hi; norm_num)
    (by norm_num)
    (by intro i hi; exact hx i)
  simp only [smul_eq_mul] at hj
  have havg0 : 0 ≤ (∑ i, x i) / 3 := by
    apply div_nonneg _ (by norm_num)
    exact Finset.sum_nonneg (fun i _ => (hx i).1)
  have havg : (∑ i, x i) / 3 ≤ a := by linarith
  have hmono : Real.binEntropy ((∑ i, x i) / 3) ≤ Real.binEntropy a := by
    apply Real.binEntropy_strictMonoOn.monotoneOn
    · exact ⟨havg0, by linarith⟩
    · exact ⟨ha0, by linarith⟩
    · exact havg
  have hsumx : (∑ i : Fin 3, (1 / 3 : ℝ) * x i) = (∑ i, x i) / 3 := by
    rw [← Finset.mul_sum]
    ring
  have hsumH : (∑ i : Fin 3, (1 / 3 : ℝ) * Real.binEntropy (x i)) =
      (∑ i, Real.binEntropy (x i)) / 3 := by
    rw [← Finset.mul_sum]
    ring
  rw [hsumx, hsumH] at hj
  linarith

/-- FC2K's exact three-count entropy bound for a smaller-side cut. -/
theorem fc2k_entropy_tuple_bound {n s : ℕ} (hs : 0 < s) (hhalf : 2 * s ≤ n)
    (j : Fin 3 → Fin (s + 1)) (hbad : 400 * (∑ i, (j i).val) < 199 * s) :
    (∑ i : Fin 3, ((s : ℝ) * Real.binEntropy ((j i).val / (s : ℝ)) +
      ((n - s : ℕ) : ℝ) * Real.binEntropy ((j i).val / ((n - s : ℕ) : ℝ)))) ≤
      3 * ((s : ℝ) * Real.binEntropy ((199 : ℝ) / 1200) +
        ((n - s : ℕ) : ℝ) * Real.binEntropy (((199 : ℝ) / 1200) * s / ((n - s : ℕ) : ℝ))) := by
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs
  have hns : s ≤ n - s := by omega
  have hnspos : (0 : ℝ) < (n - s : ℕ) := by exact_mod_cast (show 0 < n - s by omega)
  have hsle : (s : ℝ) ≤ (n - s : ℕ) := by exact_mod_cast hns
  have hjle (i : Fin 3) : ((j i).val : ℝ) ≤ s := by exact_mod_cast Nat.le_of_lt_succ (j i).isLt
  have hbadR : (400 : ℝ) * (∑ i, ((j i).val : ℝ)) < 199 * s := by
    exact_mod_cast hbad
  have hbound1 : (∑ i, ((j i).val : ℝ) / s) ≤ 3 * ((199 : ℝ) / 1200) := by
    rw [← Finset.sum_div]
    apply (div_le_iff₀ hspos).2
    linarith
  have hbound2 : (∑ i, ((j i).val : ℝ) / ((n - s : ℕ) : ℝ)) ≤
      3 * (((199 : ℝ) / 1200) * s / ((n - s : ℕ) : ℝ)) := by
    rw [← Finset.sum_div]
    apply (div_le_iff₀ hnspos).2
    have hcancel : (3 * (((199 : ℝ) / 1200) * s / ((n - s : ℕ) : ℝ))) *
        ((n - s : ℕ) : ℝ) = 3 * ((199 : ℝ) / 1200) * s := by
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
  have hb0 : 0 ≤ ((199 : ℝ) / 1200) * s / ((n - s : ℕ) : ℝ) := by positivity
  have hb1 : ((199 : ℝ) / 1200) * s / ((n - s : ℕ) : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ hnspos).2
    nlinarith
  have h1 := entropy_sum_three_le _ (199 / 1200) hx1 (by norm_num) (by norm_num) hbound1
  have h2 := entropy_sum_three_le _ (((199 : ℝ) / 1200) * s / ((n - s : ℕ) : ℝ))
    hx2 hb0 hb1 hbound2
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  nlinarith

/-- Every bad three-count tuple has its hypergeometric numerator bounded by
the source's common entropy exponential. -/
theorem fc2k_tuple_choose_entropy_bound {n s : ℕ} (hs : 0 < s) (hhalf : 2 * s ≤ n)
    (j : Fin 3 → Fin (s + 1)) (hbad : 400 * (∑ i, (j i).val) < 199 * s) :
    (∏ i, ((s.choose (j i).val : ℕ) : ℝ) * (((n - s).choose (j i).val : ℕ) : ℝ)) ≤
      Real.exp (3 * ((s : ℝ) * Real.binEntropy ((199 : ℝ) / 1200) +
        ((n - s : ℕ) : ℝ) * Real.binEntropy (((199 : ℝ) / 1200) * s / ((n - s : ℕ) : ℝ)))) := by
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
    _ ≤ _ := (Real.exp_le_exp).2 (fc2k_entropy_tuple_bound hs hhalf j hbad)

/-- The complete fixed-cut hypergeometric numerator is bounded by the
number of possible count triples times the common entropy exponential. -/
theorem fc2k_cutWeight_entropy_bound {n s : ℕ} (hs : 0 < s) (hhalf : 2 * s ≤ n) :
    (permutationCutWeight n s : ℝ) ≤ ((s + 1 : ℕ) : ℝ)^3 *
      Real.exp (3 * ((s : ℝ) * Real.binEntropy ((199 : ℝ) / 1200) +
        ((n - s : ℕ) : ℝ) * Real.binEntropy (((199 : ℝ) / 1200) * s / ((n - s : ℕ) : ℝ)))) := by
  classical
  let A : Finset (Fin 3 → Fin (s + 1)) := Finset.univ.filter
    (fun j => 400 * (∑ i, (j i).val) < 199 * min s (n - s))
  let C : ℝ := Real.exp (3 * ((s : ℝ) * Real.binEntropy ((199 : ℝ) / 1200) +
        ((n - s : ℕ) : ℝ) * Real.binEntropy (((199 : ℝ) / 1200) * s / ((n - s : ℕ) : ℝ))))
  have hmin : min s (n - s) = s := Nat.min_eq_left (by omega)
  have hterm (j : Fin 3 → Fin (s + 1)) (hj : j ∈ A) :
      (∏ i, ((s.choose (j i).val : ℕ) : ℝ) * (((n - s).choose (j i).val : ℕ) : ℝ)) ≤ C := by
    have hbad := (Finset.mem_filter.mp hj).2
    rw [hmin] at hbad
    exact fc2k_tuple_choose_entropy_bound hs hhalf j hbad
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
  simpa [permutationCutWeight, A, C] using hfinal

/-- Scaling the cut entropy by the number of vertices gives exactly the
source numerator-minus-denominator entropy expression. -/
theorem fc2k_cut_entropy_scaling {n s : ℕ} (hs : 0 < s) (hhalf : 2 * s ≤ n) :
    3 * ((s : ℝ) * Real.binEntropy ((199 : ℝ) / 1200) +
      ((n - s : ℕ) : ℝ) * Real.binEntropy (((199 : ℝ) / 1200) * s / ((n - s : ℕ) : ℝ))) -
      2 * (n : ℝ) * Real.binEntropy ((s : ℝ) / n) =
        (n : ℝ) * fc2kCutEntropy ((s : ℝ) / n) := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hns : ((n - s : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show n - s ≠ 0 by omega)
  have hsub : ((n - s : ℕ) : ℝ) = (n : ℝ) - s := Nat.cast_sub (by omega)
  have hcomp : 1 - (s : ℝ) / n = ((n - s : ℕ) : ℝ) / n := by
    rw [hsub]
    field_simp
  have hratio : ((199 : ℝ) / 1200) * ((s : ℝ) / n) / (1 - (s : ℝ) / n) =
      ((199 : ℝ) / 1200) * s / ((n - s : ℕ) : ℝ) := by
    rw [hcomp]
    field_simp
  unfold fc2kCutEntropy
  rw [hratio, hcomp]
  field_simp

/-- The large-cut union-bound summand, normalized by the uniform triple
sample-space cardinality, is bounded by the source entropy expression. -/
theorem fc2k_fixedCut_large_entropy_bound {n s : ℕ} (hs : 0 < s) (hhalf : 2 * s ≤ n) :
    ((Nat.choose n s : ℝ) * (permutationFixedCutCount n s : ℝ)) / (n.factorial : ℝ)^3 ≤
      ((n + 1 : ℕ) : ℝ)^2 * ((s + 1 : ℕ) : ℝ)^3 *
        Real.exp ((n : ℝ) * fc2kCutEntropy ((s : ℝ) / n)) := by
  let C : ℝ := Nat.choose n s
  let F : ℝ := n.factorial
  let W : ℝ := permutationCutWeight n s
  let H : ℝ := (n : ℝ) * Real.binEntropy ((s : ℝ) / n)
  let E : ℝ := 3 * ((s : ℝ) * Real.binEntropy ((199 : ℝ) / 1200) +
    ((n - s : ℕ) : ℝ) * Real.binEntropy (((199 : ℝ) / 1200) * s / ((n - s : ℕ) : ℝ)))
  have hC : 0 < C := by dsimp [C]; exact_mod_cast Nat.choose_pos (by omega : s ≤ n)
  have hF : 0 < F := by dsimp [F]; exact_mod_cast Nat.factorial_pos n
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hchoose := binomial_exp_entropy_le_succ_mul_choose_all (show s ≤ n by omega)
  have hdiv : 1 / C ≤ ((n + 1 : ℕ) : ℝ) / Real.exp H := by
    apply (div_le_div_iff₀ hC (Real.exp_pos H)).2
    simpa [C, H] using hchoose
  have hsquare := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 / C by positivity) hdiv 2
  have hw : W ≤ ((s + 1 : ℕ) : ℝ)^3 * Real.exp E := by
    simpa [W, E] using fc2k_cutWeight_entropy_bound hs hhalf
  have heq : C^3 * (permutationFixedCutCount n s : ℝ) = F^3 * W := by
    dsimp [C, F, W]
    exact_mod_cast permutationFixedCutCount_scaled (show s ≤ n by omega)
  have hnorm : C * (permutationFixedCutCount n s : ℝ) / F^3 = W * (1 / C)^2 := by
    have hCne := ne_of_gt hC
    have hFne := ne_of_gt hF
    field_simp
    nlinarith [heq]
  change C * (permutationFixedCutCount n s : ℝ) / F^3 ≤ _
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
      have hscale : E - 2 * H = (n : ℝ) * fc2kCutEntropy ((s : ℝ) / n) := by
        dsimp [E, H]
        nlinarith [fc2k_cut_entropy_scaling hs hhalf]
      rw [hscale]

/-- On the actual large-cut interval each normalized cut-size summand has
uniform exponential decay. -/
theorem fc2k_large_cut_summand_bound {n s : ℕ} (hs : 0 < s) (hhalf : 2 * s ≤ n)
    (hlarge : n ≤ 256 * s) :
    ((Nat.choose n s : ℝ) * (permutationFixedCutCount n s : ℝ)) / (n.factorial : ℝ)^3 ≤
      ((n + 1 : ℕ) : ℝ)^5 * Real.exp (-(n : ℝ) / 34) := by
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
  have hent := fc2k_entropy_interval_gate ht0 ht1
  have hexp : Real.exp ((n : ℝ) * fc2kCutEntropy ((s : ℝ) / n)) ≤
      Real.exp (-(n : ℝ) / 34) := by
    apply (Real.exp_le_exp).2
    nlinarith
  have hsp : ((s + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show s + 1 ≤ n + 1 by omega)
  have hpowers : ((s + 1 : ℕ) : ℝ)^3 ≤ ((n + 1 : ℕ) : ℝ)^3 :=
    pow_le_pow_left₀ (by positivity) hsp 3
  calc
    _ ≤ ((n + 1 : ℕ) : ℝ)^2 * ((s + 1 : ℕ) : ℝ)^3 *
        Real.exp ((n : ℝ) * fc2kCutEntropy ((s : ℝ) / n)) :=
      fc2k_fixedCut_large_entropy_bound hs hhalf
    _ ≤ ((n + 1 : ℕ) : ℝ)^2 * ((n + 1 : ℕ) : ℝ)^3 * Real.exp (-(n : ℝ) / 34) := by
      gcongr
    _ = _ := by ring

/-- Summing the large-cut estimates costs at most one factor `n+1`; no
independence between different cuts is used. -/
theorem fc2k_large_cut_sum_bound {n : ℕ} (hn : 0 < n) :
    ((∑ s ∈ permutationLargeSizes n, Nat.choose n s * permutationFixedCutCount n s : ℕ) : ℝ) /
      (n.factorial : ℝ)^3 ≤ ((n + 1 : ℕ) : ℝ)^6 * Real.exp (-(n : ℝ) / 34) := by
  classical
  let A := permutationLargeSizes n
  let C : ℝ := ((n + 1 : ℕ) : ℝ)^5 * Real.exp (-(n : ℝ) / 34)
  have hsum : (∑ s ∈ A, ((Nat.choose n s : ℝ) * (permutationFixedCutCount n s : ℝ)) /
      (n.factorial : ℝ)^3) ≤ (A.card : ℝ) * C := by
    have h := Finset.sum_le_card_nsmul A
      (fun s => ((Nat.choose n s : ℝ) * (permutationFixedCutCount n s : ℝ)) /
        (n.factorial : ℝ)^3) C (by
        intro s hs
        have hs' := (Finset.mem_filter.mp hs).2
        have hspos : 0 < s := by omega
        exact fc2k_large_cut_summand_bound hspos hs'.1 hs'.2)
    simpa using h
  have hcard : A.card ≤ n + 1 := by
    have hsub : A ⊆ Finset.range (n + 1) := Finset.filter_subset _ _
    simpa using Finset.card_le_card hsub
  have hcardR : (A.card : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsum' := hsum.trans (mul_le_mul_of_nonneg_right hcardR hC)
  have hsumid : ((∑ s ∈ A, Nat.choose n s * permutationFixedCutCount n s : ℕ) : ℝ) /
      (n.factorial : ℝ)^3 = ∑ s ∈ A,
        ((Nat.choose n s : ℝ) * (permutationFixedCutCount n s : ℝ)) / (n.factorial : ℝ)^3 := by
    push_cast
    rw [Finset.sum_div]
  rw [hsumid]
  calc
    _ ≤ ((n + 1 : ℕ) : ℝ) * C := hsum'
    _ = _ := by dsimp [C]; ring

/-- FC2K1 pays the large-cut union bound with room for the derangement
conditioning budget. -/
theorem fc2k_large_cut_decay {n : ℕ} (hn : 2001 ≤ n) :
    ((n + 1 : ℕ) : ℝ)^6 * Real.exp (-(n : ℝ) / 34) < 1 / 216 := by
  have hnR : (2001 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hgate := fc2k_large_cut_gate hnR
  have hpowexp : Real.exp (6 * Real.log (4 * (n : ℝ))) = (4 * (n : ℝ))^6 := by
    rw [show (6 : ℝ) = (6 : ℕ) by norm_num, Real.exp_nat_mul, Real.exp_log (by positivity)]
  have hexp8 : Real.exp (Real.log 8) = 8 := Real.exp_log (by norm_num)
  have hexp : (4 * (n : ℝ))^6 * 8 * Real.exp (-(n : ℝ) / 34) < 1 := by
    have h := (Real.exp_lt_exp).2 (show 6 * Real.log (4 * (n : ℝ)) + Real.log 8 - (n : ℝ) / 34 < 0 by linarith)
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, hpowexp, hexp8, Real.exp_zero] at h
    simpa [neg_div] using h
  have hbase : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by push_cast; linarith
  have hpow := pow_le_pow_left₀ (show (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by positivity) hbase 6
  have hmul := mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg (-(n : ℝ) / 34))
  have hident : (4 * (n : ℝ))^6 * 8 * Real.exp (-(n : ℝ) / 34) =
      512 * ((2 * (n : ℝ))^6 * Real.exp (-(n : ℝ) / 34)) := by ring
  rw [hident] at hexp
  nlinarith

/-- The entire large-cut union costs strictly less than one eighth of the
one-in-27 derangement conditioning budget. -/
theorem fc2k_large_cut_integer_budget {n : ℕ} (hn : 2001 ≤ n) :
    216 * (∑ s ∈ permutationLargeSizes n, Nat.choose n s * permutationFixedCutCount n s) <
      (n.factorial)^3 := by
  have hsum := (fc2k_large_cut_sum_bound (show 0 < n by omega)).trans_lt (fc2k_large_cut_decay hn)
  have hF : 0 < (n.factorial : ℝ)^3 := pow_pos (by exact_mod_cast Nat.factorial_pos n) _
  have hreal : (216 : ℝ) *
      ((∑ s ∈ permutationLargeSizes n, Nat.choose n s * permutationFixedCutCount n s : ℕ) : ℝ) <
        (n.factorial : ℝ)^3 := by
    have h := (div_lt_iff₀ hF).1 hsum
    nlinarith
  exact_mod_cast hreal

end
end Sude
