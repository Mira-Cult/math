import Sude.StageFairSwapMoment

/-! A finite Chernoff and union-bound selection principle. Labels can encode
both orientations of each line. No geometry or independence between labelled
scores is assumed. -/
namespace Sude
noncomputable section
open MeasureTheory ProbabilityTheory

/-- If the sum of the labelled Chernoff bounds is below one, a single
uniformly sampled finite outcome meets every strict upper bound. -/
theorem finite_uniform_simultaneous_exists {α L : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype L]
    (score : L → α → ℝ) (threshold t momentBound : L → ℝ)
    (ht : ∀ l, 0 ≤ t l)
    (hmoment : ∀ l, (∑ a, Real.exp (t l * score l a)) / Fintype.card α ≤ momentBound l)
    (hbudget : (∑ l, Real.exp (-t l * threshold l) * momentBound l) < 1) :
    ∃ a, ∀ l, score l a < threshold l := by
  classical
  let μ : Measure α := uniformOn (Set.univ : Set α)
  have : IsProbabilityMeasure μ := inferInstance
  let bad : L → Set α := fun l => {a | threshold l ≤ score l a}
  have hsingle (l : L) : μ.real (bad l) ≤ Real.exp (-t l * threshold l) * momentBound l := by
    have hi : Integrable (fun a => Real.exp (t l * score l a)) μ := Integrable.of_finite
    have hm : mgf (score l) μ (t l) ≤ momentBound l := by
      change μ[fun a => Real.exp (t l * score l a)] ≤ _
      rw [finite_uniform_integral_eq_average]
      exact hmoment l
    calc
      μ.real (bad l) ≤ Real.exp (-t l * threshold l) * mgf (score l) μ (t l) :=
        measure_ge_le_exp_mul_mgf (threshold l) (ht l) hi
      _ ≤ _ := mul_le_mul_of_nonneg_left hm (le_of_lt (Real.exp_pos _))
  have hfail : μ.real (⋃ l, bad l) < 1 :=
    ((measureReal_iUnion_fintype_le bad).trans (Finset.sum_le_sum (fun l _ => hsingle l))).trans_lt hbudget
  by_contra hnone
  have hcover : (⋃ l, bad l) = Set.univ := by
    ext a
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    by_contra hn
    apply hnone
    refine ⟨a, ?_⟩
    intro l
    apply lt_of_not_ge
    intro h
    exact hn ⟨l, h⟩
  rw [hcover] at hfail
  simp at hfail


local instance finiteSelectionPermMeasurable (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

/-- Two-sided simultaneous selection for a single joint stage assignment and
swap vector. A separate moment bound is assumed for each sign and line; the
bounds may be obtained from `stage_fair_swap_exp_moment`. -/
theorem stage_swap_simultaneous_exists {ι L : Type*} [Fintype ι] [DecidableEq ι] [Fintype L]
    (r n : ℕ) (score : L → (Fin r → Equiv.Perm (Fin n)) → (ι → Bool) → ℝ)
    (threshold t : L → ℝ) (momentBound : L → Bool → ℝ)
    (ht : ∀ l, 0 ≤ t l)
    (hmoment : ∀ l b, (∑ a, ∑ ω : ι → Bool,
       Real.exp (t l * (if b then score l a ω else -score l a ω))) /
       ((Fintype.card (Fin r → Equiv.Perm (Fin n)) : ℝ) * (2 : ℝ) ^ Fintype.card ι) ≤
         momentBound l b)
    (hbudget : (∑ l, ∑ b, Real.exp (-t l * threshold l) * momentBound l b) < 1) :
    ∃ a ω, ∀ l, |score l a ω| < threshold l := by
  classical
  let X : (L × Bool) → ((Fin r → Equiv.Perm (Fin n)) × (ι → Bool)) → ℝ :=
    fun lb z => if lb.2 then score lb.1 z.1 z.2 else -score lb.1 z.1 z.2
  have h := finite_uniform_simultaneous_exists X
    (fun lb => threshold lb.1) (fun lb => t lb.1) (fun lb => momentBound lb.1 lb.2)
    (fun lb => ht lb.1) (by
      intro ⟨l, b⟩
      simpa [X, Fintype.sum_prod_type, Fintype.card_prod, Fintype.card_fun,
        Fintype.card_bool, Nat.cast_mul, Nat.cast_pow] using hmoment l b)
    (by simpa [Fintype.sum_prod_type] using hbudget)
  obtain ⟨⟨a, ω⟩, ha⟩ := h
  refine ⟨a, ω, fun l => ?_⟩
  apply abs_lt.mpr
  constructor
  · have hneg := ha (l, false)
    simp only [X, Bool.false_eq_true, ↓reduceIte] at hneg
    linarith
  · simpa [X] using ha (l, true)



/-- The mixed stage/swap moment bound yields one joint assignment satisfying
all two-sided labelled bounds, whenever the displayed sum is below one.
Each sign may use its own representation of the same labelled score. -/
theorem stage_fair_swap_simultaneous_exists {ι L : Type*} [Fintype ι] [DecidableEq ι] [Fintype L]
    (r n : ℕ) (score : L → (Fin r → Equiv.Perm (Fin n)) → (ι → Bool) → ℝ)
    (outer : L → Bool → (Fin r → Equiv.Perm (Fin n)) → ℝ)
    (x y : L → Bool → (Fin r → Equiv.Perm (Fin n)) → ι → ℝ)
    (w₁ w₂ lo hi : L → Bool → ι → ℝ) (threshold t : L → ℝ)
    (ht : ∀ l, 0 ≤ t l)
    (hx : ∀ l b a i, x l b a i ∈ Set.Icc (lo l b i) (hi l b i))
    (hy : ∀ l b a i, y l b a i ∈ Set.Icc (lo l b i) (hi l b i))
    (hscore : ∀ l b a ω, (if b then score l a ω else -score l a ω) =
      outer l b a + ∑ i,
        (fairBlockSwapValue (x l b a i) (y l b a i) (w₁ l b i) (w₂ l b i) (ω i) -
          (w₁ l b i + w₂ l b i) * (x l b a i + y l b a i) / 2))
    (hbudget : (∑ l, ∑ b, Real.exp (-t l * threshold l) *
      (mgf (outer l b) (stagePermutationMeasure r n) (t l) *
        ∏ i, Real.exp (t l ^ 2 * ((w₁ l b i - w₂ l b i) ^ 2 *
          (hi l b i - lo l b i) ^ 2 / 4) / 2))) < 1) :
    ∃ a ω, ∀ l, |score l a ω| < threshold l := by
  classical
  apply stage_swap_simultaneous_exists r n score threshold t
    (fun l b => mgf (outer l b) (stagePermutationMeasure r n) (t l) *
      ∏ i, Real.exp (t l ^ 2 * ((w₁ l b i - w₂ l b i) ^ 2 *
        (hi l b i - lo l b i) ^ 2 / 4) / 2)) ht
  · intro l b
    simpa only [hscore l b] using stage_fair_swap_exp_moment r n (outer l b)
      (x l b) (y l b) (w₁ l b) (w₂ l b) (lo l b) (hi l b) (t l) (hx l b) (hy l b)
  · exact hbudget


end
end Sude
