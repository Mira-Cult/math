import Sude.PrefixLabelSelectionAdapter
import Sude.CentralStock
import Sude.PoolWidth
import Sude.CentralPhysicalPlacement
import Sude.PrefixSelectionMeanShift

/-! DQ1--DQ2: select two successive batches from an entire labelled stock.
These results do not place the labels in diagonal cells or prove line bounds. -/
namespace Sude
noncomputable section

/-- Select a batch close to the actual mean of the full stock. Labels remain
distinct even when their values coincide; empty and full selections are allowed. -/
theorem full_stock_label_select {α : Type*} [DecidableEq α]
    (stock : Finset α) (value : α → ℝ) (q : ℕ) (W : ℝ)
    (hW : 0 ≤ W) (hq : q ≤ stock.card)
    (hwidth : ∀ x ∈ stock, ∀ y ∈ stock, value y - value x ≤ W) :
    ∃ T : Finset α, T ⊆ stock ∧ T.card = q ∧
      |(∑ x ∈ T, value x) - (q : ℝ) * centralEntriesMean stock value| ≤ W / 2 := by
  classical
  obtain ⟨T, hT, herror⟩ := prefix_global_finset_select (J := Unit)
    (fun _ => stock) q (fun _ => value) W hW (fun _ => hq)
    (fun _ => hwidth)
  refine ⟨T (), (hT ()).1, (hT ()).2, ?_⟩
  simpa [centralEntriesMean] using herror

/-- The two successive mean-relative errors combine to at most one full width. -/
theorem full_stock_two_batch_error {α : Type*} [DecidableEq α]
    (A T U : Finset α) (v : α → ℝ) (W : ℝ)
    (hT : T ⊆ A) (hU : U ⊆ A \ T)
    (hpos : 0 < (A \ T).card)
    (hfirst : |(∑ x ∈ T, v x) - (T.card : ℝ) * centralEntriesMean A v| ≤ W / 2)
    (hsecond : |(∑ x ∈ U, v x) - (U.card : ℝ) * centralEntriesMean (A \ T) v| ≤ W / 2) :
    Disjoint T U ∧ (T ∪ U).card = T.card + U.card ∧
    |(∑ x ∈ T ∪ U, v x) - ((T.card + U.card : ℕ) : ℝ) * centralEntriesMean A v| ≤ W := by
  classical
  have hrem : (A \ T).card = A.card - T.card := Finset.card_sdiff_of_subset hT
  have h := prefix_cumulative_selection_deviation (Finset.univ : Finset Unit)
    (fun _ => A) (fun _ => T) (fun _ => U) (fun _ => v)
    A.card T.card U.card (by simp [hT]) (by simp) (by simp)
    (by simp [hU]) (by simp) (by omega)
  have hid : (∑ x ∈ T ∪ U, v x) - ((T.card + U.card : ℕ) : ℝ) * centralEntriesMean A v =
      (1 - (U.card : ℝ) / ((A \ T).card : ℝ)) *
        ((∑ x ∈ T, v x) - (T.card : ℝ) * centralEntriesMean A v) +
        ((∑ x ∈ U, v x) - (U.card : ℝ) * centralEntriesMean (A \ T) v) := by
    simpa [centralEntriesMean, hrem] using h.2
  have hq : U.card ≤ (A \ T).card := Finset.card_le_card hU
  have hden : (0 : ℝ) < (A \ T).card := by exact_mod_cast hpos
  have hqreal : (U.card : ℝ) ≤ (A \ T).card := by exact_mod_cast hq
  have hfrac : 0 ≤ (U.card : ℝ) / (A \ T).card ∧ (U.card : ℝ) / (A \ T).card ≤ 1 := by
    constructor
    · positivity
    · exact (div_le_one hden).2 hqreal
  have hcoef : 0 ≤ 1 - (U.card : ℝ) / (A \ T).card ∧
      1 - (U.card : ℝ) / (A \ T).card ≤ 1 := by constructor <;> linarith [hfrac.1,hfrac.2]
  have hbound : |(1 - (U.card : ℝ) / ((A \ T).card : ℝ)) *
        ((∑ x ∈ T, v x) - (T.card : ℝ) * centralEntriesMean A v) +
        ((∑ x ∈ U, v x) - (U.card : ℝ) * centralEntriesMean (A \ T) v)| ≤ W := by
    calc
      _ ≤ |(1 - (U.card : ℝ) / ((A \ T).card : ℝ)) *
        ((∑ x ∈ T, v x) - (T.card : ℝ) * centralEntriesMean A v)| +
        |(∑ x ∈ U, v x) - (U.card : ℝ) * centralEntriesMean (A \ T) v| := abs_add_le _ _
      _ = (1 - (U.card : ℝ) / ((A \ T).card : ℝ)) *
        |(∑ x ∈ T, v x) - (T.card : ℝ) * centralEntriesMean A v| +
        |(∑ x ∈ U, v x) - (U.card : ℝ) * centralEntriesMean (A \ T) v| := by rw [abs_mul, abs_of_nonneg hcoef.1]
      _ ≤ W := by
        have hh := mul_le_mul hcoef.2 hfirst (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
        linarith
  refine ⟨?_, ?_, ?_⟩
  · exact (h.1 () (Finset.mem_univ ())).1
  · exact (h.1 () (Finset.mem_univ ())).2
  · rw [hid]; exact hbound

/-- Select both diagonal batches in sequence from one labelled stock. The
second discrepancy is measured against the actual mean after the first batch.
The hypotheses ensure a nonempty final remainder for subsequent mean updates. -/
theorem full_stock_two_batches {α : Type*} [DecidableEq α]
    (stock : Finset α) (value : α → ℝ) (q₁ q₂ : ℕ) (W : ℝ)
    (hW : 0 ≤ W) (hroom : q₁ + q₂ < stock.card)
    (hwidth : ∀ x ∈ stock, ∀ y ∈ stock, value y - value x ≤ W) :
    ∃ T U : Finset α,
      T ⊆ stock ∧ U ⊆ stock \ T ∧ T.card = q₁ ∧ U.card = q₂ ∧
      |(∑ x ∈ T, value x) - (q₁ : ℝ) * centralEntriesMean stock value| ≤ W / 2 ∧
      |(∑ x ∈ U, value x) - (q₂ : ℝ) * centralEntriesMean (stock \ T) value| ≤ W / 2 ∧
      0 < ((stock \ T) \ U).card ∧
      |(∑ x ∈ T ∪ U, value x) - ((q₁ + q₂ : ℕ) : ℝ) *
        centralEntriesMean stock value| ≤ W := by
  have hq₁ : q₁ ≤ stock.card := by omega
  obtain ⟨T, hT, hcardT, herrorT⟩ := full_stock_label_select stock value q₁ W hW hq₁ hwidth
  have hcard : (stock \ T).card + q₁ = stock.card := by
    simpa [hcardT] using Finset.card_sdiff_add_card_eq_card hT
  have hq₂ : q₂ ≤ (stock \ T).card := by omega
  have hwidth' : ∀ x ∈ stock \ T, ∀ y ∈ stock \ T, value y - value x ≤ W := by
    intro x hx y hy
    exact hwidth x (Finset.mem_sdiff.mp hx).1 y (Finset.mem_sdiff.mp hy).1
  obtain ⟨U, hU, hcardU, herrorU⟩ :=
    full_stock_label_select (stock \ T) value q₂ W hW hq₂ hwidth'
  have hcard' : ((stock \ T) \ U).card + q₂ = (stock \ T).card := by
    simpa [hcardU] using Finset.card_sdiff_add_card_eq_card hU
  have hpos : 0 < (stock \ T).card := by omega
  have hcombined := full_stock_two_batch_error stock T U value W hT hU hpos
    (by simpa [hcardT] using herrorT) (by simpa [hcardU] using herrorU)
  refine ⟨T, U, hT, hU, hcardT, hcardU, herrorT, herrorU, by omega, ?_⟩
  simpa [hcardT, hcardU] using hcombined.2.2

/-- DQ1--DQ2 selection from the exact values unused by the supplied physical
reservation. This uses the pool-width theorem and no prime-density input. -/
theorem actual_unused_pool_two_batches {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (reserved : Finset (Cell n)) (q₁ q₂ : ℕ)
    (hroom : q₁ + q₂ < (actualUnusedPool a reserved).card) :
    ∃ T U : Finset (pool n),
      T ⊆ actualUnusedPool a reserved ∧ U ⊆ actualUnusedPool a reserved \ T ∧
      T.card = q₁ ∧ U.card = q₂ ∧
      |(∑ x ∈ T, centralPoolValue x) - (q₁ : ℝ) *
        centralEntriesMean (actualUnusedPool a reserved) centralPoolValue| ≤ (poolMaximum n : ℝ) / 2 ∧
      |(∑ x ∈ U, centralPoolValue x) - (q₂ : ℝ) *
        centralEntriesMean (actualUnusedPool a reserved \ T) centralPoolValue| ≤ (poolMaximum n : ℝ) / 2 ∧
      0 < ((actualUnusedPool a reserved \ T) \ U).card ∧
      |(∑ x ∈ T ∪ U, centralPoolValue x) - ((q₁ + q₂ : ℕ) : ℝ) *
        centralEntriesMean (actualUnusedPool a reserved) centralPoolValue| ≤ (poolMaximum n : ℝ) := by
  apply full_stock_two_batches (actualUnusedPool a reserved) centralPoolValue q₁ q₂
    (poolMaximum n : ℝ) (by positivity) hroom
  intro x hx y hy
  exact le_of_lt (actual_unused_pool_strict_width a reserved y hy x hx)

end
end Sude
