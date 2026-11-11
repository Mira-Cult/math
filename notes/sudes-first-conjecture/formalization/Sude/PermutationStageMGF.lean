import Sude.PermutationWeightedInduction
import Mathlib.Probability.Independence.Basic

/-! Independent whole-stage permutations with without-replacement slots. -/
namespace Sude
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
local instance stagePermMeasurable (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

/-- Independent uniform permutations, one whole permutation per stage. -/
def stagePermutationMeasure (r n : ℕ) : Measure (Fin r → Equiv.Perm (Fin n)) :=
  Measure.pi (fun _ => uniformPermutation n)

theorem stagePermutationMeasure_isProbability (r n : ℕ) :
    IsProbabilityMeasure (stagePermutationMeasure r n) := by
  have : IsProbabilityMeasure (uniformPermutation n) := uniformPermutation_isProbability n
  unfold stagePermutationMeasure
  infer_instance

/-- The empty history is the original uniform permutation space. -/
theorem permutationHistoryMeasure_empty {n : ℕ} (reference : Equiv.Perm (Fin n)) :
    permutationHistoryMeasure ∅ reference = uniformPermutation n := by
  unfold permutationHistoryMeasure uniformPermutation
  congr 1
  ext p
  simp [permutationHistory]

/-- A stage's weighted contribution centered by its actual uniform mean. -/
def stageWeightedCentered {r n : ℕ} (slots : Fin r → Finset (Fin n))
    (weights values : Fin r → Fin n → ℝ) (i : Fin r) (p : Equiv.Perm (Fin n)) : ℝ :=
  permutationWeightedCentered ∅ (slots i) (Equiv.refl (Fin n)) (weights i) (values i) p

/-- Variance proxy summed over independent whole-stage permutations. -/
def stageWeightedProxy {r n : ℕ} (slots : Fin r → Finset (Fin n))
    (weights : Fin r → Fin n → ℝ) (lo upper : Fin r → ℝ) : NNReal :=
  ∑ i, permutationWeightedProxy (slots i) (weights i) (lo i) (upper i)

/-- Independent stage permutations combine the one-stage moment bounds;
within a stage, slot images remain sampled without replacement. -/
theorem stageWeighted_hasSubgaussian {r n : ℕ} (slots : Fin r → Finset (Fin n))
    (weights values : Fin r → Fin n → ℝ) (lo upper : Fin r → ℝ)
    (hnonneg : ∀ i j, j ∈ slots i → 0 ≤ weights i j)
    (hvalues : ∀ i a, values i a ∈ Set.Icc (lo i) (upper i)) :
    HasSubgaussianMGF (fun ω : Fin r → Equiv.Perm (Fin n) =>
      ∑ i, stageWeightedCentered slots weights values i (ω i))
      (stageWeightedProxy slots weights lo upper) (stagePermutationMeasure r n) := by
  classical
  have : IsProbabilityMeasure (uniformPermutation n) := uniformPermutation_isProbability n
  let μ : Fin r → Measure (Equiv.Perm (Fin n)) := fun _ => uniformPermutation n
  let X : Fin r → Equiv.Perm (Fin n) → ℝ := stageWeightedCentered slots weights values
  have hm : ∀ i, AEMeasurable (X i) (μ i) := fun i => Measurable.of_discrete.aemeasurable
  have hind : iIndepFun (fun i ω => X i (ω i)) (Measure.pi μ) := iIndepFun_pi hm
  change HasSubgaussianMGF (fun ω => ∑ i ∈ (Finset.univ : Finset (Fin r)), X i (ω i))
    (∑ i ∈ (Finset.univ : Finset (Fin r)), permutationWeightedProxy (slots i) (weights i) (lo i) (upper i))
    (Measure.pi μ)
  apply HasSubgaussianMGF.sum_of_iIndepFun hind
  intro i hi
  have hs := permutationWeighted_hasSubgaussian ∅ (slots i) (Equiv.refl (Fin n))
    (weights i) (values i) (lo i) (upper i) (by simp) (fun j hj => hnonneg i j hj) (hvalues i)
  rw [permutationHistoryMeasure_empty] at hs
  have hmap : Measure.map (fun ω : Fin r → Equiv.Perm (Fin n) => ω i) (Measure.pi μ) = μ i :=
    (measurePreserving_eval μ i).map_eq
  have hs' : HasSubgaussianMGF (X i) (permutationWeightedProxy (slots i) (weights i) (lo i) (upper i))
      (Measure.map (fun ω : Fin r → Equiv.Perm (Fin n) => ω i) (Measure.pi μ)) := by
    rw [hmap]
    exact hs
  exact HasSubgaussianMGF.of_map (measurable_pi_apply i).aemeasurable hs'

/-- Two-sided tail bound for the sum of all independent whole stages. -/
theorem stageWeighted_two_sided {r n : ℕ} (slots : Fin r → Finset (Fin n))
    (weights values : Fin r → Fin n → ℝ) (lo upper : Fin r → ℝ) (ε : ℝ)
    (hnonneg : ∀ i j, j ∈ slots i → 0 ≤ weights i j)
    (hvalues : ∀ i a, values i a ∈ Set.Icc (lo i) (upper i)) (hε : 0 ≤ ε) :
    (stagePermutationMeasure r n).real
      {ω | ε ≤ |∑ i, stageWeightedCentered slots weights values i (ω i)|} ≤
      2 * Real.exp (-ε ^ 2 / (2 * ((stageWeightedProxy slots weights lo upper : NNReal) : ℝ))) := by
  let μ := stagePermutationMeasure r n
  let X : (Fin r → Equiv.Perm (Fin n)) → ℝ := fun ω =>
    ∑ i, stageWeightedCentered slots weights values i (ω i)
  have : IsProbabilityMeasure μ := stagePermutationMeasure_isProbability r n
  have hsub := stageWeighted_hasSubgaussian slots weights values lo upper hnonneg hvalues
  have hpos : μ.real {ω | ε ≤ X ω} ≤
      Real.exp (-ε ^ 2 / (2 * ((stageWeightedProxy slots weights lo upper : NNReal) : ℝ))) :=
    hsub.measure_ge_le hε
  have hneg : μ.real {ω | ε ≤ -X ω} ≤
      Real.exp (-ε ^ 2 / (2 * ((stageWeightedProxy slots weights lo upper : NNReal) : ℝ))) := by
    simpa using hsub.neg.measure_ge_le hε
  have hset : {ω | ε ≤ |X ω|} ⊆ {ω | ε ≤ X ω} ∪ {ω | ε ≤ -X ω} := by
    intro ω hω
    by_cases hx : 0 ≤ X ω
    · left
      simpa [abs_of_nonneg hx] using hω
    · right
      simpa [abs_of_nonpos (le_of_not_ge hx)] using hω
  calc
    μ.real {ω | ε ≤ |X ω|} ≤ μ.real ({ω | ε ≤ X ω} ∪ {ω | ε ≤ -X ω}) := measureReal_mono hset
    _ ≤ μ.real {ω | ε ≤ X ω} + μ.real {ω | ε ≤ -X ω} := measureReal_union_le _ _
    _ ≤ _ := by linarith [hpos, hneg]

/-- The summed proxy is exactly the source's stagewise range-squared and
squared-weight invoice, divided by four. -/
theorem stageWeightedProxy_real {r n : ℕ} (slots : Fin r → Finset (Fin n))
    (weights : Fin r → Fin n → ℝ) (lo upper : Fin r → ℝ)
    (hlu : ∀ i, lo i ≤ upper i)
    (hnonneg : ∀ i j, j ∈ slots i → 0 ≤ weights i j) :
    ((stageWeightedProxy slots weights lo upper : NNReal) : ℝ) =
      ∑ i, ((upper i - lo i) ^ 2 / 4) * ∑ j ∈ slots i, (weights i j) ^ 2 := by
  unfold stageWeightedProxy
  rw [NNReal.coe_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact permutationWeightedProxy_real (slots i) (weights i) (lo i) (upper i) (hlu i)
    (fun j hj => hnonneg i j hj)

/-- The centered weighted contribution to one labelled line from all stages. -/
def stageLineCentered {m r n : ℕ} (slots : Fin m → Fin r → Finset (Fin n))
    (weights : Fin m → Fin r → Fin n → ℝ) (values : Fin r → Fin n → ℝ)
    (line : Fin m) (ω : Fin r → Equiv.Perm (Fin n)) : ℝ :=
  ∑ i, stageWeightedCentered (slots line) (weights line) values i (ω i)

/-- Union bound over labelled line events. The line events need not be
independent or distinct. -/
theorem stageLines_failure_bound {m r n : ℕ} (slots : Fin m → Fin r → Finset (Fin n))
    (weights : Fin m → Fin r → Fin n → ℝ) (values : Fin r → Fin n → ℝ)
    (lo upper : Fin r → ℝ) (ε : Fin m → ℝ)
    (hnonneg : ∀ l i j, j ∈ slots l i → 0 ≤ weights l i j)
    (hvalues : ∀ i a, values i a ∈ Set.Icc (lo i) (upper i)) (hε : ∀ l, 0 ≤ ε l) :
    (stagePermutationMeasure r n).real
      {ω | ∃ l, ε l ≤ |stageLineCentered slots weights values l ω|} ≤
      ∑ l, 2 * Real.exp (-(ε l) ^ 2 /
        (2 * ((stageWeightedProxy (slots l) (weights l) lo upper : NNReal) : ℝ))) := by
  let μ := stagePermutationMeasure r n
  let bad : Fin m → Set (Fin r → Equiv.Perm (Fin n)) := fun l =>
    {ω | ε l ≤ |stageLineCentered slots weights values l ω|}
  have hevent : {ω | ∃ l, ε l ≤ |stageLineCentered slots weights values l ω|} = ⋃ l, bad l := by
    ext ω
    simp [bad]
  change μ.real {ω | ∃ l, ε l ≤ |stageLineCentered slots weights values l ω|} ≤ _
  rw [hevent]
  calc
    μ.real (⋃ l, bad l) ≤ ∑ l, μ.real (bad l) := measureReal_iUnion_fintype_le bad
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro l hl
      exact stageWeighted_two_sided (slots l) (weights l) values lo upper (ε l)
        (hnonneg l) hvalues (hε l)

/-- If the proved sum of failure bounds is below one, one assignment makes
every labelled line satisfy its error budget. -/
theorem stageLines_simultaneous_exists {m r n : ℕ} (slots : Fin m → Fin r → Finset (Fin n))
    (weights : Fin m → Fin r → Fin n → ℝ) (values : Fin r → Fin n → ℝ)
    (lo upper : Fin r → ℝ) (ε : Fin m → ℝ)
    (hnonneg : ∀ l i j, j ∈ slots l i → 0 ≤ weights l i j)
    (hvalues : ∀ i a, values i a ∈ Set.Icc (lo i) (upper i)) (hε : ∀ l, 0 ≤ ε l)
    (hbudget : (∑ l, 2 * Real.exp (-(ε l) ^ 2 /
      (2 * ((stageWeightedProxy (slots l) (weights l) lo upper : NNReal) : ℝ)))) < 1) :
    ∃ ω : Fin r → Equiv.Perm (Fin n), ∀ l, |stageLineCentered slots weights values l ω| < ε l := by
  let μ := stagePermutationMeasure r n
  have : IsProbabilityMeasure μ := stagePermutationMeasure_isProbability r n
  have hfail : μ.real {ω | ∃ l, ε l ≤ |stageLineCentered slots weights values l ω|} < 1 :=
    (stageLines_failure_bound slots weights values lo upper ε hnonneg hvalues hε).trans_lt hbudget
  by_contra hnone
  have hcover : {ω | ∃ l, ε l ≤ |stageLineCentered slots weights values l ω|} = Set.univ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    by_contra hn
    apply hnone
    refine ⟨ω, ?_⟩
    intro l
    apply lt_of_not_ge
    intro hl
    exact hn ⟨l, hl⟩
  rw [hcover] at hfail
  simp at hfail

/-- A zero proxy forces the centered stage sum to vanish almost surely.
In particular, a nonnegative threshold has zero strict-failure probability. -/
theorem stageWeighted_zero_proxy_strict_failure {r n : ℕ} (slots : Fin r → Finset (Fin n))
    (weights values : Fin r → Fin n → ℝ) (lo upper : Fin r → ℝ) (ε : ℝ)
    (hnonneg : ∀ i j, j ∈ slots i → 0 ≤ weights i j)
    (hvalues : ∀ i a, values i a ∈ Set.Icc (lo i) (upper i)) (hε : 0 ≤ ε)
    (hzero : stageWeightedProxy slots weights lo upper = 0) :
    (stagePermutationMeasure r n).real
      {ω | ε < |∑ i, stageWeightedCentered slots weights values i (ω i)|} = 0 := by
  let μ := stagePermutationMeasure r n
  let X : (Fin r → Equiv.Perm (Fin n)) → ℝ := fun ω =>
    ∑ i, stageWeightedCentered slots weights values i (ω i)
  have hsub0 : HasSubgaussianMGF X 0 μ := by
    simpa [hzero] using stageWeighted_hasSubgaussian slots weights values lo upper hnonneg hvalues
  have hAE : ∀ᵐ ω ∂μ, X ω = 0 := hsub0.ae_eq_zero_of_hasSubgaussianMGF_zero
  have hnot : ∀ᵐ ω ∂μ, ¬ ε < |X ω| := by
    filter_upwards [hAE] with ω hω
    simp [hω, not_lt_of_ge hε]
  have hnull : μ {ω | ε < |X ω|} = 0 := by
    have h := ae_iff.mp hnot
    simpa only [not_not] using h
  change μ.real {ω | ε < |X ω|} = 0
  simp [Measure.real, hnull]

/-- A zero-aware upper bound for a single line's strict failure event. -/
def stageStrictFailureBound {r n : ℕ} (slots : Fin r → Finset (Fin n))
    (weights : Fin r → Fin n → ℝ) (lo upper : Fin r → ℝ) (ε : ℝ) : ℝ :=
  if stageWeightedProxy slots weights lo upper = 0 then 0 else
    2 * Real.exp (-ε ^ 2 / (2 * ((stageWeightedProxy slots weights lo upper : NNReal) : ℝ)))

theorem stageWeighted_strict_failure_bound {r n : ℕ} (slots : Fin r → Finset (Fin n))
    (weights values : Fin r → Fin n → ℝ) (lo upper : Fin r → ℝ) (ε : ℝ)
    (hnonneg : ∀ i j, j ∈ slots i → 0 ≤ weights i j)
    (hvalues : ∀ i a, values i a ∈ Set.Icc (lo i) (upper i)) (hε : 0 ≤ ε) :
    (stagePermutationMeasure r n).real
      {ω | ε < |∑ i, stageWeightedCentered slots weights values i (ω i)|} ≤
      stageStrictFailureBound slots weights lo upper ε := by
  classical
  by_cases hz : stageWeightedProxy slots weights lo upper = 0
  · rw [stageStrictFailureBound, if_pos hz,
      stageWeighted_zero_proxy_strict_failure slots weights values lo upper ε hnonneg hvalues hε hz]
  · rw [stageStrictFailureBound, if_neg hz]
    have hsub : {ω : Fin r → Equiv.Perm (Fin n) | ε < |∑ i, stageWeightedCentered slots weights values i (ω i)|} ⊆
        {ω : Fin r → Equiv.Perm (Fin n) | ε ≤ |∑ i, stageWeightedCentered slots weights values i (ω i)|} := by
      intro ω hω
      change ε < |∑ i, stageWeightedCentered slots weights values i (ω i)| at hω
      change ε ≤ |∑ i, stageWeightedCentered slots weights values i (ω i)|
      exact le_of_lt hω
    have : IsProbabilityMeasure (stagePermutationMeasure r n) := stagePermutationMeasure_isProbability r n
    exact (measureReal_mono hsub).trans
      (stageWeighted_two_sided slots weights values lo upper ε hnonneg hvalues hε)

/-- Zero-aware union bound for strict failure, with no distinctness or
independence assumption on the labelled lines. -/
theorem stageLines_strict_failure_bound {m r n : ℕ} (slots : Fin m → Fin r → Finset (Fin n))
    (weights : Fin m → Fin r → Fin n → ℝ) (values : Fin r → Fin n → ℝ)
    (lo upper : Fin r → ℝ) (ε : Fin m → ℝ)
    (hnonneg : ∀ l i j, j ∈ slots l i → 0 ≤ weights l i j)
    (hvalues : ∀ i a, values i a ∈ Set.Icc (lo i) (upper i)) (hε : ∀ l, 0 ≤ ε l) :
    (stagePermutationMeasure r n).real
      {ω | ∃ l, ε l < |stageLineCentered slots weights values l ω|} ≤
      ∑ l, stageStrictFailureBound (slots l) (weights l) lo upper (ε l) := by
  let μ := stagePermutationMeasure r n
  let bad : Fin m → Set (Fin r → Equiv.Perm (Fin n)) := fun l =>
    {ω | ε l < |stageLineCentered slots weights values l ω|}
  have hevent : {ω | ∃ l, ε l < |stageLineCentered slots weights values l ω|} = ⋃ l, bad l := by
    ext ω
    simp [bad]
  change μ.real {ω | ∃ l, ε l < |stageLineCentered slots weights values l ω|} ≤ _
  rw [hevent]
  calc
    μ.real (⋃ l, bad l) ≤ ∑ l, μ.real (bad l) := measureReal_iUnion_fintype_le bad
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro l hl
      exact stageWeighted_strict_failure_bound (slots l) (weights l) values lo upper (ε l)
        (hnonneg l) hvalues (hε l)

/-- The zero-aware budget yields one placement of the stage values whose
labelled line errors all satisfy their non-strict bounds. -/
theorem stageLines_simultaneous_exists_le {m r n : ℕ} (slots : Fin m → Fin r → Finset (Fin n))
    (weights : Fin m → Fin r → Fin n → ℝ) (values : Fin r → Fin n → ℝ)
    (lo upper : Fin r → ℝ) (ε : Fin m → ℝ)
    (hnonneg : ∀ l i j, j ∈ slots l i → 0 ≤ weights l i j)
    (hvalues : ∀ i a, values i a ∈ Set.Icc (lo i) (upper i)) (hε : ∀ l, 0 ≤ ε l)
    (hbudget : (∑ l, stageStrictFailureBound (slots l) (weights l) lo upper (ε l)) < 1) :
    ∃ ω : Fin r → Equiv.Perm (Fin n), ∀ l, |stageLineCentered slots weights values l ω| ≤ ε l := by
  let μ := stagePermutationMeasure r n
  have : IsProbabilityMeasure μ := stagePermutationMeasure_isProbability r n
  have hfail : μ.real {ω | ∃ l, ε l < |stageLineCentered slots weights values l ω|} < 1 :=
    (stageLines_strict_failure_bound slots weights values lo upper ε hnonneg hvalues hε).trans_lt hbudget
  by_contra hnone
  have hcover : {ω | ∃ l, ε l < |stageLineCentered slots weights values l ω|} = Set.univ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    by_contra hn
    apply hnone
    refine ⟨ω, ?_⟩
    intro l
    apply le_of_not_gt
    intro hl
    exact hn ⟨l, hl⟩
  rw [hcover] at hfail
  simp at hfail

end
end Sude
