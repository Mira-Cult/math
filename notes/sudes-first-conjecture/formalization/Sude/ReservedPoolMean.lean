import Sude.CentralPhysicalPlacement
import Sude.ActualUnusedPool
import Sude.FTTTargetList


/-! Mean accounting for the exact prescribed pool and physical reservations. -/
namespace Sude
noncomputable section

/-- The entire prescribed pool as a finite set of values. -/
def prescribedPoolValues (n : ℕ) : Finset (pool n) :=
  (Finset.univ : Finset (Fin (n * n))).image (poolEquiv n)

@[simp] theorem mem_prescribedPoolValues {n : ℕ} (v : pool n) : v ∈ prescribedPoolValues n := by
  exact Finset.mem_image.mpr ⟨(poolEquiv n).symm v, Finset.mem_univ _, (poolEquiv n).apply_symm_apply v⟩

/-- The finite pool mean is the source's exact total `T` divided by `n²`. -/
theorem prescribedPoolValues_mean (n : ℕ) :
    centralEntriesMean (prescribedPoolValues n) centralPoolValue =
      (Lucas.poolTotal n : ℝ) / (n * n : ℕ) := by
  classical
  have hcard : (prescribedPoolValues n).card = n * n := by
    unfold prescribedPoolValues
    rw [Finset.card_image_of_injective _ (poolEquiv n).injective]
    simp
  have hsum : (∑ v ∈ prescribedPoolValues n, centralPoolValue v) = (Lucas.poolTotal n : ℝ) := by
    unfold prescribedPoolValues
    rw [Finset.sum_image (by intro x _ y _ h; exact (poolEquiv n).injective h)]
    simp [centralPoolValue, Lucas.poolTotal, Nat.cast_sum]
  unfold centralEntriesMean
  rw [hcard, hsum]

/-- The unused pool is the full prescribed pool with exactly the values in
reserved cells removed. -/
theorem actualUnusedPool_eq_full_sdiff {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (reserved : Finset (Cell n)) :
    actualUnusedPool a reserved = prescribedPoolValues n \ reserved.image (entryPool a) := by
  classical
  ext v
  rw [mem_actualUnusedPool]
  simp only [Finset.mem_sdiff, mem_prescribedPoolValues, true_and, Finset.mem_image, not_exists]
  constructor
  · intro h z hz
    have hv := congrArg Subtype.val hz.2
    exact h z hz.1 hv.symm
  · intro h z hz he
    exact h z ⟨hz, Subtype.ext he.symm⟩

/-- Exact mean shift after reserving physical cells, bounded by their total
signed deviation from the original prescribed-pool mean. -/
theorem actual_unused_mean_from_reserved_error {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (reserved : Finset (Cell n)) (δ : ℝ)
    (hpos : 0 < (actualUnusedPool a reserved).card)
    (herr : |(∑ z ∈ reserved, (entry a z : ℝ)) -
      (reserved.card : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤ δ) :
    |centralEntriesMean (actualUnusedPool a reserved) centralPoolValue -
        centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤
      δ / (actualUnusedPool a reserved).card := by
  classical
  let chosen := reserved.image (entryPool a)
  let μ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
  have hsub : chosen ⊆ prescribedPoolValues n := fun v _ => mem_prescribedPoolValues v
  have heq : (prescribedPoolValues n) \ chosen = actualUnusedPool a reserved :=
    (actualUnusedPool_eq_full_sdiff a reserved).symm
  have hpos' : 0 < ((prescribedPoolValues n) \ chosen).card := by rw [heq]; exact hpos
  have hmean := central_entries_actual_mean_update (prescribedPoolValues n) chosen
    centralPoolValue hsub hpos'
  have hcard : chosen.card = reserved.card :=
    Finset.card_image_of_injective _ (entryPool a).injective
  have hsum : (∑ v ∈ chosen, centralPoolValue v) = ∑ z ∈ reserved, (entry a z : ℝ) := by
    dsimp [chosen]
    rw [Finset.sum_image]
    · rfl
    · intro x _ y _ h
      exact (entryPool a).injective h
  rw [heq, hcard, hsum] at hmean
  have hden : (0 : ℝ) < (actualUnusedPool a reserved).card := by exact_mod_cast hpos
  have he : centralEntriesMean (actualUnusedPool a reserved) centralPoolValue - μ =
      -(((∑ z ∈ reserved, (entry a z : ℝ)) - (reserved.card : ℝ) * μ) /
        (actualUnusedPool a reserved).card) := by rw [hmean]; ring
  rw [he, abs_neg, abs_div, abs_of_pos hden]
  exact div_le_div_of_nonneg_right herr hden.le

/-- The signed error of actual, globally distinct reserved pairs is bounded
by the sum of their individual midpoint budgets. -/
theorem reserved_pairs_total_error {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (a : Cell n ≃ Fin (n * n)) (reserved : Finset (Cell n))
    (pair : I × Bool → Cell n) (budget : I → ℝ)
    (hinj : Function.Injective pair)
    (hcover : (Finset.univ : Finset (I × Bool)).image pair = reserved)
    (hpair : ∀ i, |(entry a (pair (i, true)) : ℝ) + (entry a (pair (i, false)) : ℝ) -
      2 * centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤ budget i) :
    |(∑ z ∈ reserved, (entry a z : ℝ)) -
      (reserved.card : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤
        ∑ i, budget i := by
  classical
  let μ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
  have hsum : (∑ z ∈ reserved, (entry a z : ℝ)) =
      ∑ i : I, ((entry a (pair (i, true)) : ℝ) + (entry a (pair (i, false)) : ℝ)) := by
    rw [← hcover, Finset.sum_image (by intro x _ y _ h; exact hinj h), Fintype.sum_prod_type]
    simp
  have hcard : reserved.card = Fintype.card I * 2 := by
    rw [← hcover, Finset.card_image_of_injective _ hinj]
    simp [Fintype.card_prod]
  have heq : (∑ z ∈ reserved, (entry a z : ℝ)) - (reserved.card : ℝ) * μ =
      ∑ i : I, ((entry a (pair (i, true)) : ℝ) + (entry a (pair (i, false)) : ℝ) - 2 * μ) := by
    rw [hsum, hcard]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [heq]
  calc
    _ ≤ ∑ i : I, |(entry a (pair (i, true)) : ℝ) + (entry a (pair (i, false)) : ℝ) - 2 * μ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, budget i := Finset.sum_le_sum (by intro i _; exact hpair i)

/-- With every reservation accounted for by distinct pairs, their midpoint
budgets control the actual unused-pool mean. -/
theorem actual_unused_mean_from_reserved_pairs {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (a : Cell n ≃ Fin (n * n)) (reserved : Finset (Cell n))
    (pair : I × Bool → Cell n) (budget : I → ℝ)
    (hinj : Function.Injective pair)
    (hcover : (Finset.univ : Finset (I × Bool)).image pair = reserved)
    (hpos : 0 < (actualUnusedPool a reserved).card)
    (hpair : ∀ i, |(entry a (pair (i, true)) : ℝ) + (entry a (pair (i, false)) : ℝ) -
      2 * centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤ budget i) :
    |centralEntriesMean (actualUnusedPool a reserved) centralPoolValue -
      centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤
        (∑ i, budget i) / (actualUnusedPool a reserved).card :=
  actual_unused_mean_from_reserved_error a reserved (∑ i, budget i) hpos
    (reserved_pairs_total_error a reserved pair budget hinj hcover hpair)

/-- The exact post-reservation count, including the natural-number domain. -/
theorem actualUnusedPool_card_eq_sub {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (reserved : Finset (Cell n)) :
    (actualUnusedPool a reserved).card = n * n - reserved.card := by
  have hc := actualUnusedPool_card n a reserved
  omega

/-- Pair-midpoint accounting in the source's `T/n²` normalization, with the
actual remaining-cardinality denominator and explicit positivity condition. -/
theorem actual_unused_mean_from_reserved_pairs_source {n : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I] (a : Cell n ≃ Fin (n * n)) (reserved : Finset (Cell n))
    (pair : I × Bool → Cell n) (budget : I → ℝ)
    (hinj : Function.Injective pair)
    (hcover : (Finset.univ : Finset (I × Bool)).image pair = reserved)
    (hreserved : reserved.card < n * n)
    (hpair : ∀ i, |(entry a (pair (i, true)) : ℝ) + (entry a (pair (i, false)) : ℝ) -
      2 * ((Lucas.poolTotal n : ℝ) / (n * n : ℕ))| ≤ budget i) :
    |centralEntriesMean (actualUnusedPool a reserved) centralPoolValue -
      (Lucas.poolTotal n : ℝ) / (n * n : ℕ)| ≤
        (∑ i, budget i) / (n * n - reserved.card : ℕ) := by
  have hpos : 0 < (actualUnusedPool a reserved).card := by
    rw [actualUnusedPool_card_eq_sub]
    omega
  have hp : ∀ i, |(entry a (pair (i, true)) : ℝ) + (entry a (pair (i, false)) : ℝ) -
      2 * centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤ budget i := by
    simpa only [prescribedPoolValues_mean] using hpair
  have h := actual_unused_mean_from_reserved_pairs a reserved pair budget hinj hcover hpos hp
  simpa only [prescribedPoolValues_mean, actualUnusedPool_card_eq_sub] using h

end
end Sude
