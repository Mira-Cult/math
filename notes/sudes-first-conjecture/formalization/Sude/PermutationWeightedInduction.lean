import Sude.PermutationWeightedMGF
import Mathlib.Data.Finset.Max

/-! Exponential moments of weighted samples from a finite permutation. -/
namespace Sude
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
local instance weightedInductionPermMeasurable (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

/-- Weighted permutation Hoeffding moment bound, conditional on any
realizable history, proved by revealing the largest remaining weight. -/
theorem permutationWeighted_mgf_bound {n : ℕ} (positions slots : Finset (Fin n))
    (reference : Equiv.Perm (Fin n)) (weights values : Fin n → ℝ) (lo upper : ℝ)
    (hdis : Disjoint slots positions) (hnonneg : ∀ j ∈ slots, 0 ≤ weights j)
    (hvalues : ∀ a, values a ∈ Set.Icc lo upper) (t : ℝ) :
    mgf (permutationWeightedCentered positions slots reference weights values)
      (permutationHistoryMeasure positions reference) t ≤
      Real.exp (((permutationWeightedProxy slots weights lo upper : NNReal) : ℝ) * t ^ 2 / 2) := by
  classical
  induction slots using Finset.strongInductionOn generalizing positions reference with
  | _ slots ih =>
    by_cases hnonempty : slots.Nonempty
    · obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image slots weights hnonempty
      have hi' : i ∉ positions := (Finset.disjoint_left.mp hdis) hi
      let tail := slots.erase i
      have htail : tail ⊂ slots := Finset.erase_ssubset hi
      have htaildis : Disjoint tail (insert i positions) := by
        apply Finset.disjoint_left.mpr
        intro j hj hjinsert
        have hjtail : j ∈ slots.erase i := hj
        simp only [Finset.mem_erase] at hjtail
        simp only [Finset.mem_insert] at hjinsert
        rcases hjinsert with rfl | hjinsert
        · exact hjtail.1 rfl
        · exact (Finset.disjoint_left.mp hdis) hjtail.2 hjinsert
      have htailnonneg : ∀ j ∈ tail, 0 ≤ weights j := by
        intro j hj
        exact hnonneg j (Finset.mem_of_mem_erase hj)
      have horder : ∀ j ∈ slots.erase i, weights j ≤ weights i := by
        intro j hj
        exact hmax j (Finset.mem_of_mem_erase hj)
      by_cases hK : 2 ≤ n - positions.card
      · let R : Equiv.Perm (Fin n) → ℝ := fun p =>
          permutationWeightedCentered (insert i positions) tail p weights values p
        let B : ℝ := Real.exp (((permutationWeightedProxy tail weights lo upper : NNReal) : ℝ) * t ^ 2 / 2)
        have hB : 0 ≤ B := le_of_lt (Real.exp_pos _)
        have hfuture (a : {a // a ∈ (positions.image reference)ᶜ}) :
            mgf R (permutationHistoryMeasure (insert i positions)
              (permutationHistoryExtension positions reference i hi' a)) t ≤ B := by
          let e := permutationHistoryExtension positions reference i hi' a
          let ν := permutationHistoryMeasure (insert i positions) e
          have hae := permutationWeighted_future_ae positions tail reference i hi' a weights values
          have hEq : mgf R ν t =
              mgf (permutationWeightedCentered (insert i positions) tail e weights values) ν t :=
            mgf_congr hae
          rw [hEq]
          exact ih tail htail (insert i positions) e htaildis htailnonneg
        have hstep := permutationRevealIncrement_mgf_step positions slots reference i hi' hK hdis hi
          weights values lo upper hnonneg horder (fun a _ => hvalues a) R t B hB hfuture
        have hcent : permutationWeightedCentered positions slots reference weights values =
            fun p => permutationRevealIncrement positions slots reference i weights values p + R p := by
          funext p
          exact permutationWeightedCentered_decompose positions slots reference p i hi weights values
        have hproxy : permutationWeightedProxy tail weights lo upper +
            (‖weights i * upper - weights i * lo‖₊ / 2) ^ 2 =
              permutationWeightedProxy slots weights lo upper := by
          exact Finset.sum_erase_add slots
            (fun j => (‖weights j * upper - weights j * lo‖₊ / 2) ^ 2) hi
        have hproxyR := congrArg (fun z : NNReal => (z : ℝ)) hproxy
        simp only [NNReal.coe_add] at hproxyR
        rw [hcent]
        calc
          _ ≤ B * Real.exp (((‖weights i * upper - weights i * lo‖₊ / 2) ^ 2 : NNReal) * t ^ 2 / 2) := hstep
          _ = _ := by
            dsimp [B]
            rw [← Real.exp_add]
            congr 1
            calc
              _ = (((permutationWeightedProxy tail weights lo upper : NNReal) : ℝ) +
                (((‖weights i * upper - weights i * lo‖₊ / 2) ^ 2 : NNReal) : ℝ)) * t ^ 2 / 2 := by
                  simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm, Real.norm_eq_abs]
                  ring
              _ = _ := by rw [hproxyR]
      · have hlt : positions.card < n := by simpa using Finset.card_lt_univ_of_notMem hi'
        have hKone : n - positions.card = 1 := by omega
        have hsingle := permutationHistory_last_remaining positions slots i hi' hKone hdis hi
        let μ := permutationHistoryMeasure positions reference
        have hlast := permutationHistory_last_subgaussian positions slots reference i hi' hKone hdis hi weights values
        have hlast' : HasSubgaussianMGF (permutationRevealIncrement positions slots reference i weights values)
            (permutationWeightedProxy slots weights lo upper) μ := by
          apply subgaussian_parameter_mono hlast
          exact zero_le
        have hcent : permutationWeightedCentered positions slots reference weights values =
            permutationRevealIncrement positions slots reference i weights values := by
          funext p
          simp [permutationWeightedCentered, permutationWeightedSum, permutationRevealIncrement, hsingle]
        rw [hcent]
        exact hlast'.mgf_le t
    · have hempty : slots = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
      subst slots
      have : IsProbabilityMeasure (permutationHistoryMeasure positions reference) :=
        permutationHistoryMeasure_isProbability positions reference
      have hzero : permutationWeightedCentered positions ∅ reference weights values =
          (fun _ => 0) := by
        funext p
        simp [permutationWeightedCentered, permutationWeightedSum]
      rw [hzero]
      simp [permutationWeightedProxy]

/-- Every real function on a finite permutation-history probability space is
integrable. -/
theorem permutationHistory_integrable {n : ℕ} (positions : Finset (Fin n))
    (reference : Equiv.Perm (Fin n)) (F : Equiv.Perm (Fin n) → ℝ) :
    Integrable F (permutationHistoryMeasure positions reference) := by
  have hcount : Integrable F (Measure.count : Measure (Equiv.Perm (Fin n))) := by
    apply integrable_count_iff.mpr
    exact Summable.of_finite
  have hrest : Integrable F ((Measure.count : Measure (Equiv.Perm (Fin n))).restrict
      (permutationHistory positions reference : Set (Equiv.Perm (Fin n)))) := hcount.integrableOn
  have hpos : 0 < (permutationHistory positions reference).card := by
    apply Finset.card_pos.mpr
    exact ⟨reference, by simp [permutationHistory]⟩
  have hcountne : (Measure.count : Measure (Equiv.Perm (Fin n)))
      (permutationHistory positions reference : Set (Equiv.Perm (Fin n))) ≠ 0 := by
    rw [Measure.count_apply_finset]
    exact_mod_cast (Nat.ne_of_gt hpos)
  change Integrable F (((Measure.count : Measure (Equiv.Perm (Fin n)))
      (permutationHistory positions reference : Set (Equiv.Perm (Fin n))))⁻¹ •
      (Measure.count : Measure (Equiv.Perm (Fin n))).restrict
        (permutationHistory positions reference : Set (Equiv.Perm (Fin n))))
  exact hrest.smul_measure (ENNReal.inv_ne_top.mpr hcountne)

/-- The complete one-permutation, without-replacement Hoeffding moment bound. -/
theorem permutationWeighted_hasSubgaussian {n : ℕ} (positions slots : Finset (Fin n))
    (reference : Equiv.Perm (Fin n)) (weights values : Fin n → ℝ) (lo upper : ℝ)
    (hdis : Disjoint slots positions) (hnonneg : ∀ j ∈ slots, 0 ≤ weights j)
    (hvalues : ∀ a, values a ∈ Set.Icc lo upper) :
    HasSubgaussianMGF (permutationWeightedCentered positions slots reference weights values)
      (permutationWeightedProxy slots weights lo upper) (permutationHistoryMeasure positions reference) := by
  refine ⟨?_, ?_⟩
  · intro t
    exact permutationHistory_integrable positions reference _
  · intro t
    exact permutationWeighted_mgf_bound positions slots reference weights values lo upper
      hdis hnonneg hvalues t

/-- Two-sided conditional Hoeffding bound for one weighted permutation. -/
theorem permutationWeighted_two_sided {n : ℕ} (positions slots : Finset (Fin n))
    (reference : Equiv.Perm (Fin n)) (weights values : Fin n → ℝ) (lo upper ε : ℝ)
    (hdis : Disjoint slots positions) (hnonneg : ∀ j ∈ slots, 0 ≤ weights j)
    (hvalues : ∀ a, values a ∈ Set.Icc lo upper) (hε : 0 ≤ ε) :
    (permutationHistoryMeasure positions reference).real
      {p | ε ≤ |permutationWeightedCentered positions slots reference weights values p|} ≤
      2 * Real.exp (-ε ^ 2 / (2 * ((permutationWeightedProxy slots weights lo upper : NNReal) : ℝ))) := by
  let μ := permutationHistoryMeasure positions reference
  let X := permutationWeightedCentered positions slots reference weights values
  have : IsProbabilityMeasure μ := permutationHistoryMeasure_isProbability positions reference
  have hsub := permutationWeighted_hasSubgaussian positions slots reference weights values lo upper
    hdis hnonneg hvalues
  have hpos : μ.real {p | ε ≤ X p} ≤
      Real.exp (-ε ^ 2 / (2 * ((permutationWeightedProxy slots weights lo upper : NNReal) : ℝ))) :=
    hsub.measure_ge_le hε
  have hneg : μ.real {p | ε ≤ -X p} ≤
      Real.exp (-ε ^ 2 / (2 * ((permutationWeightedProxy slots weights lo upper : NNReal) : ℝ))) := by
    simpa using hsub.neg.measure_ge_le hε
  have hset : {p | ε ≤ |X p|} ⊆ {p | ε ≤ X p} ∪ {p | ε ≤ -X p} := by
    intro p hp
    by_cases hx : 0 ≤ X p
    · left
      simpa [abs_of_nonneg hx] using hp
    · right
      simpa [abs_of_nonpos (le_of_not_ge hx)] using hp
  calc
    μ.real {p | ε ≤ |X p|} ≤ μ.real ({p | ε ≤ X p} ∪ {p | ε ≤ -X p}) := measureReal_mono hset
    _ ≤ μ.real {p | ε ≤ X p} + μ.real {p | ε ≤ -X p} := measureReal_union_le _ _
    _ ≤ _ := by linarith [hpos, hneg]

/-- The nonnegative-real proxy is exactly the source's range-squared times
the sum of squared weights, divided by four. -/
theorem permutationWeightedProxy_real {n : ℕ} (slots : Finset (Fin n))
    (weights : Fin n → ℝ) (lo upper : ℝ) (hlu : lo ≤ upper)
    (hnonneg : ∀ j ∈ slots, 0 ≤ weights j) :
    ((permutationWeightedProxy slots weights lo upper : NNReal) : ℝ) =
      ((upper - lo) ^ 2 / 4) * ∑ j ∈ slots, (weights j) ^ 2 := by
  unfold permutationWeightedProxy
  rw [NNReal.coe_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat, coe_nnnorm, Real.norm_eq_abs]
  have hproduct : 0 ≤ weights j * (upper - lo) := mul_nonneg (hnonneg j hj) (sub_nonneg.mpr hlu)
  rw [show weights j * upper - weights j * lo = weights j * (upper - lo) by ring,
    abs_of_nonneg hproduct]
  ring

end
end Sude
