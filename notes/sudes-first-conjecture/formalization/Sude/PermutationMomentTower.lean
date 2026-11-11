import Sude.PermutationTower
import Sude.PermutationExposure

/-! Composing moment bounds through the actual permutation-history tower. -/
namespace Sude
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
local instance momentTowerPermMeasurable (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

/-- A pointwise comparison of all next-history integrals propagates to the
current history. No independence between the next value and the future is
assumed. -/
theorem permutationHistory_integral_compare_of_next {n : ℕ} (positions : Finset (Fin n))
    (reference : Equiv.Perm (Fin n)) (i : Fin n) (hi : i ∉ positions)
    (F G : Equiv.Perm (Fin n) → ℝ) (C : ℝ)
    (hbound : ∀ a : {a // a ∈ (positions.image reference)ᶜ},
      (permutationHistoryMeasure (insert i positions)
        (permutationHistoryExtension positions reference i hi a))[F] ≤
      C * (permutationHistoryMeasure (insert i positions)
        (permutationHistoryExtension positions reference i hi a))[G]) :
    (permutationHistoryMeasure positions reference)[F] ≤
      C * (permutationHistoryMeasure positions reference)[G] := by
  classical
  let available : Finset (Fin n) := (positions.image reference)ᶜ
  let K : ℝ := (n - positions.card : ℕ)
  have hK : 0 ≤ K := by positivity
  have hsum : (∑ a ∈ available.attach,
      (permutationHistoryMeasure (insert i positions)
        (permutationHistoryExtension positions reference i hi a))[F]) ≤
      C * (∑ a ∈ available.attach,
        (permutationHistoryMeasure (insert i positions)
          (permutationHistoryExtension positions reference i hi a))[G]) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    exact hbound a
  rw [permutationHistory_integral_tower positions reference i hi F,
    permutationHistory_integral_tower positions reference i hi G]
  change (∑ a ∈ available.attach,
      (permutationHistoryMeasure (insert i positions)
        (permutationHistoryExtension positions reference i hi a))[F]) / K ≤
    C * ((∑ a ∈ available.attach,
      (permutationHistoryMeasure (insert i positions)
        (permutationHistoryExtension positions reference i hi a))[G]) / K)
  calc
    _ ≤ (C * (∑ a ∈ available.attach,
      (permutationHistoryMeasure (insert i positions)
        (permutationHistoryExtension positions reference i hi a))[G])) / K :=
      div_le_div_of_nonneg_right hsum hK
    _ = _ := by ring

/-- A current increment constant on each next-value fiber can be combined
with a uniform future moment bound by the finite tower. This statement
makes no independence assumption between the current and future terms. -/
theorem permutationHistory_mgf_add_of_next_mgf {n : ℕ} (positions : Finset (Fin n))
    (reference : Equiv.Perm (Fin n)) (i : Fin n) (hi : i ∉ positions)
    (D R : Equiv.Perm (Fin n) → ℝ) (t B : ℝ)
    (hconstant : ∀ (a : {a // a ∈ (positions.image reference)ᶜ}) q,
      q ∈ permutationHistoryNext positions reference i a.val →
      D q = D (permutationHistoryExtension positions reference i hi a))
    (hfuture : ∀ a : {a // a ∈ (positions.image reference)ᶜ},
      mgf R (permutationHistoryMeasure (insert i positions)
        (permutationHistoryExtension positions reference i hi a)) t ≤ B) :
    mgf (fun p => D p + R p) (permutationHistoryMeasure positions reference) t ≤
      B * mgf D (permutationHistoryMeasure positions reference) t := by
  change (permutationHistoryMeasure positions reference)[fun p => Real.exp (t * (D p + R p))] ≤
    B * (permutationHistoryMeasure positions reference)[fun p => Real.exp (t * D p)]
  apply permutationHistory_integral_compare_of_next positions reference i hi _ _ B
  intro a
  let e := permutationHistoryExtension positions reference i hi a
  let ν := permutationHistoryMeasure (insert i positions) e
  have : IsProbabilityMeasure ν := permutationHistoryMeasure_isProbability (insert i positions) e
  have he := permutationHistoryExtension_mem positions reference i hi a
  have hset := permutationHistoryNext_eq_insert positions reference e i a.val he
  have hmem : ∀ᵐ q ∂ν, q ∈ permutationHistory (insert i positions) e := by
    change ∀ᵐ q ∂Measure.count[| (permutationHistory (insert i positions) e : Set (Equiv.Perm (Fin n)))],
      q ∈ permutationHistory (insert i positions) e
    exact ae_cond_mem (by measurability)
  have hconst : ∀ᵐ q ∂ν, D q = D e := by
    filter_upwards [hmem] with q hq
    apply hconstant a q
    rw [hset]
    exact hq
  have heF : ν[fun q => Real.exp (t * (D q + R q))] =
      Real.exp (t * D e) * mgf R ν t := by
    calc
      _ = ν[fun q => Real.exp (t * D e) * Real.exp (t * R q)] := by
        apply integral_congr_ae
        filter_upwards [hconst] with q hq
        rw [hq, mul_add, Real.exp_add]
      _ = _ := by rw [integral_const_mul]; rfl
  have heG : ν[fun q => Real.exp (t * D q)] = Real.exp (t * D e) := by
    calc
      _ = ν[fun _ => Real.exp (t * D e)] := by
        apply integral_congr_ae
        filter_upwards [hconst] with q hq
        rw [hq]
      _ = _ := by simp
  change ν[fun q => Real.exp (t * (D q + R q))] ≤
    B * ν[fun q => Real.exp (t * D q)]
  rw [heF, heG]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left (hfuture a) (le_of_lt (Real.exp_pos _))

/-- The actual change in weighted conditional mean when the next position is
revealed. -/
def permutationRevealIncrement {n : ℕ} (positions remaining : Finset (Fin n))
    (reference : Equiv.Perm (Fin n)) (i : Fin n) (weights values : Fin n → ℝ)
    (p : Equiv.Perm (Fin n)) : ℝ :=
  weights i * values (p i) +
    (permutationHistoryMeasure (insert i positions) p)[fun q =>
      ∑ j ∈ remaining.erase i, weights j * values (q j)] -
    (permutationHistoryMeasure positions reference)[fun q =>
      ∑ j ∈ remaining, weights j * values (q j)]

/-- The reveal increment depends on the new output, not on the unexposed
part of the permutation. -/
theorem permutationRevealIncrement_constant_on_next {n : ℕ}
    (positions remaining : Finset (Fin n)) (reference : Equiv.Perm (Fin n))
    (i : Fin n) (hi : i ∉ positions) (hK : 2 ≤ n - positions.card)
    (hdis : Disjoint remaining positions) (hslot : i ∈ remaining)
    (weights values : Fin n → ℝ)
    (a : {a // a ∈ (positions.image reference)ᶜ}) (q : Equiv.Perm (Fin n))
    (hq : q ∈ permutationHistoryNext positions reference i a.val) :
    permutationRevealIncrement positions remaining reference i weights values q =
      permutationRevealIncrement positions remaining reference i weights values
        (permutationHistoryExtension positions reference i hi a) := by
  let e := permutationHistoryExtension positions reference i hi a
  have he : e ∈ permutationHistoryNext positions reference i a.val :=
    permutationHistoryExtension_mem positions reference i hi a
  have hqi : q i = a.val := (Finset.mem_filter.mp hq).2
  have hei : e i = a.val := (Finset.mem_filter.mp he).2
  have hq' := permutationHistory_reveal_increment positions remaining reference q i a.val
    hi hq hK hdis hslot weights values
  have he' := permutationHistory_reveal_increment positions remaining reference e i a.val
    hi he hK hdis hslot weights values
  unfold permutationRevealIncrement
  rw [hqi, hei]
  exact hq'.trans he'.symm

/-- One nonfinal source-weighted reveal composes with an arbitrary bound on
the future centered moment on each next history. -/
theorem permutationRevealIncrement_mgf_step {n : ℕ}
    (positions remaining : Finset (Fin n)) (reference : Equiv.Perm (Fin n))
    (i : Fin n) (hi : i ∉ positions) (hK : 2 ≤ n - positions.card)
    (hdis : Disjoint remaining positions) (hslot : i ∈ remaining)
    (weights values : Fin n → ℝ) (lo upper : ℝ)
    (hnonneg : ∀ j ∈ remaining, 0 ≤ weights j)
    (horder : ∀ j ∈ remaining.erase i, weights j ≤ weights i)
    (hbound : ∀ a, a ∉ positions.image reference → values a ∈ Set.Icc lo upper)
    (R : Equiv.Perm (Fin n) → ℝ) (t B : ℝ) (hB : 0 ≤ B)
    (hfuture : ∀ a : {a // a ∈ (positions.image reference)ᶜ},
      mgf R (permutationHistoryMeasure (insert i positions)
        (permutationHistoryExtension positions reference i hi a)) t ≤ B) :
    mgf (fun p => permutationRevealIncrement positions remaining reference i weights values p + R p)
        (permutationHistoryMeasure positions reference) t ≤
      B * Real.exp (((‖weights i * upper - weights i * lo‖₊ / 2) ^ 2 : NNReal) * t ^ 2 / 2) := by
  let D := permutationRevealIncrement positions remaining reference i weights values
  let μ := permutationHistoryMeasure positions reference
  have hD : HasSubgaussianMGF D ((‖weights i * upper - weights i * lo‖₊ / 2) ^ 2) μ := by
    exact permutationHistory_reveal_source_subgaussian positions remaining reference i hi hK hdis hslot
      weights values lo upper hnonneg horder hbound
  have hcomp := permutationHistory_mgf_add_of_next_mgf positions reference i hi D R t B
    (permutationRevealIncrement_constant_on_next positions remaining reference i hi hK hdis hslot weights values)
    hfuture
  calc
    _ ≤ B * mgf D μ t := hcomp
    _ ≤ B * Real.exp (((‖weights i * upper - weights i * lo‖₊ / 2) ^ 2 : NNReal) * t ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (hD.mgf_le t) hB

end
end Sude
