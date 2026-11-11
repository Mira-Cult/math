import Sude.FiniteMomentSelection
import Mathlib.MeasureTheory.Integral.Prod

/-! A finite moment union bound on the joint stage-permutation and swap
space. No independence between score events is assumed. -/
namespace Sude
noncomputable section
open MeasureTheory ProbabilityTheory

local instance stageSwapFailurePermMeasurable (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

/-- Product integration is the normalized double average on these finite
uniform spaces. -/
theorem stage_swap_product_integral_eq_average {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r n : ℕ) (f : ((Fin r → Equiv.Perm (Fin n)) × (ι → Bool)) → ℝ) :
    ∫ z, f z ∂((stagePermutationMeasure r n).prod
      (uniformOn (Set.univ : Set (ι → Bool)))) =
      (∑ a, ∑ ω : ι → Bool, f (a,ω)) /
        ((Fintype.card (Fin r → Equiv.Perm (Fin n)) : ℝ) * (2 : ℝ)^Fintype.card ι) := by
  classical
  haveI : IsProbabilityMeasure (stagePermutationMeasure r n) := stagePermutationMeasure_isProbability r n
  haveI : IsProbabilityMeasure (uniformOn (Set.univ : Set (ι → Bool))) := inferInstance
  rw [MeasureTheory.integral_prod f (Integrable.of_finite)]
  simp_rw [finite_uniform_integral_eq_average]
  rw [stage_permutation_integral_eq_average]
  rw [← Finset.sum_div]
  simp only [Fintype.card_fun, Fintype.card_bool, Nat.cast_pow]
  rw [div_div, mul_comm]
  norm_num

/-- A normalized moment invoice bounds the actual joint-space probability of
any two-sided score failure. The bound is valid without event independence. -/
theorem stage_swap_failure_bound {ι L : Type*} [Fintype ι] [DecidableEq ι] [Fintype L]
    (r n : ℕ) (score : L → (Fin r → Equiv.Perm (Fin n)) → (ι → Bool) → ℝ)
    (threshold t : L → ℝ) (momentBound : L → Bool → ℝ)
    (ht : ∀ l, 0 ≤ t l)
    (hmoment : ∀ l b, (∑ a, ∑ ω : ι → Bool,
       Real.exp (t l * (if b then score l a ω else -score l a ω))) /
       ((Fintype.card (Fin r → Equiv.Perm (Fin n)) : ℝ) * (2 : ℝ) ^ Fintype.card ι) ≤
         momentBound l b) :
    ((stagePermutationMeasure r n).prod (uniformOn (Set.univ : Set (ι → Bool)))).real
      {z | ∃ l, threshold l ≤ |score l z.1 z.2|} ≤
      ∑ l, ∑ b, Real.exp (-t l * threshold l) * momentBound l b := by
  classical
  let ρ := (stagePermutationMeasure r n).prod (uniformOn (Set.univ : Set (ι → Bool)))
  haveI : IsProbabilityMeasure (stagePermutationMeasure r n) := stagePermutationMeasure_isProbability r n
  haveI : IsProbabilityMeasure (uniformOn (Set.univ : Set (ι → Bool))) := inferInstance
  haveI : IsProbabilityMeasure ρ := inferInstance
  let signed : (L × Bool) → ((Fin r → Equiv.Perm (Fin n)) × (ι → Bool)) → ℝ :=
    fun lb z => if lb.2 then score lb.1 z.1 z.2 else -score lb.1 z.1 z.2
  let bad : (L × Bool) → Set ((Fin r → Equiv.Perm (Fin n)) × (ι → Bool)) :=
    fun lb => {z | threshold lb.1 ≤ signed lb z}
  have hsingle (lb : L × Bool) : ρ.real (bad lb) ≤
      Real.exp (-t lb.1 * threshold lb.1) * momentBound lb.1 lb.2 := by
    have hi : Integrable (fun z => Real.exp (t lb.1 * signed lb z)) ρ := Integrable.of_finite
    have hm : mgf (signed lb) ρ (t lb.1) ≤ momentBound lb.1 lb.2 := by
      change ρ[fun z => Real.exp (t lb.1 * signed lb z)] ≤ _
      rw [stage_swap_product_integral_eq_average]
      exact hmoment lb.1 lb.2
    calc
      ρ.real (bad lb) ≤ Real.exp (-t lb.1 * threshold lb.1) * mgf (signed lb) ρ (t lb.1) :=
        measure_ge_le_exp_mul_mgf (threshold lb.1) (ht lb.1) hi
      _ ≤ _ := mul_le_mul_of_nonneg_left hm (le_of_lt (Real.exp_pos _))
  have hcover : {z | ∃ l, threshold l ≤ |score l z.1 z.2|} ⊆ ⋃ lb, bad lb := by
    intro z hz
    obtain ⟨l,hl⟩ := hz
    by_cases hs : 0 ≤ score l z.1 z.2
    · exact Set.mem_iUnion.mpr ⟨(l,true), by simpa [bad,signed,abs_of_nonneg hs] using hl⟩
    · exact Set.mem_iUnion.mpr ⟨(l,false), by simpa [bad,signed,abs_of_nonpos (le_of_not_ge hs)] using hl⟩
  calc
    _ ≤ ρ.real (⋃ lb, bad lb) := measureReal_mono hcover
    _ ≤ ∑ lb, ρ.real (bad lb) := measureReal_iUnion_fintype_le bad
    _ ≤ ∑ lb, Real.exp (-t lb.1 * threshold lb.1) * momentBound lb.1 lb.2 :=
      Finset.sum_le_sum (fun lb _ => hsingle lb)
    _ = _ := by simp only [Fintype.sum_prod_type]

end
end Sude
