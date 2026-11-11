import Sude.PermutationStageMGF

/-! The product of uniform stage-permutation measures is uniform on the
finite set of whole stage assignments. This supplies an exact bridge between
finite normalized sums and the existing probability-measure interface. -/
namespace Sude
noncomputable section
open MeasureTheory ProbabilityTheory

local instance uniformStagePermMeasurable (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

/-- On any finite discrete space, the uniform integral is the normalized
finite sum. The empty type is included, using the usual zero convention. -/
theorem finite_uniform_integral_eq_average {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (f : α → ℝ) :
    (uniformOn (Set.univ : Set α))[f] = (∑ a, f a) / Fintype.card α := by
  classical
  have hint : Integrable f (Measure.count : Measure α) := by
    apply integrable_count_iff.mpr
    exact Summable.of_finite
  have his : IntegrableOn f ((Finset.univ : Finset α) : Set α)
      (Measure.count : Measure α) := hint.integrableOn
  have hset : (Set.univ : Set α) = ((Finset.univ : Finset α) : Set α) := by simp
  rw [hset]
  unfold uniformOn ProbabilityTheory.cond
  rw [integral_smul_measure, setIntegral_finset _ his]
  simp [measureReal_def, div_eq_mul_inv, mul_comm]

/-- Independent uniformly sampled stage permutations are uniformly
distributed over all complete stage assignments, including zero stages. -/
theorem stage_permutation_measure_eq_uniform (r n : ℕ) :
    stagePermutationMeasure r n =
      uniformOn (Set.univ : Set (Fin r → Equiv.Perm (Fin n))) := by
  unfold stagePermutationMeasure uniformPermutation
  simpa using (uniformOn_pi (f := fun _ : Fin r => (Set.univ : Set (Equiv.Perm (Fin n))))).symm

/-- Integration over the stage-permutation product measure is its exact
normalized sum over whole assignments. -/
theorem stage_permutation_integral_eq_average (r n : ℕ)
    (f : (Fin r → Equiv.Perm (Fin n)) → ℝ) :
    (stagePermutationMeasure r n)[f] =
      (∑ ω, f ω) / Fintype.card (Fin r → Equiv.Perm (Fin n)) := by
  rw [stage_permutation_measure_eq_uniform]
  exact finite_uniform_integral_eq_average f

/-- The corresponding moment-generating function is the same normalized
finite exponential sum. -/
theorem stage_permutation_mgf_eq_average (r n : ℕ)
    (f : (Fin r → Equiv.Perm (Fin n)) → ℝ) (t : ℝ) :
    mgf f (stagePermutationMeasure r n) t =
      (∑ ω, Real.exp (t * f ω)) / Fintype.card (Fin r → Equiv.Perm (Fin n)) := by
  exact stage_permutation_integral_eq_average r n (fun ω => Real.exp (t * f ω))

end
end Sude
