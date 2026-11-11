import Sude.RegularFactorCompletion

/-! Place a central stock into the exceptional cells outside a supplied factor,
then complete the factor from the exact remaining pool. -/
namespace Sude
noncomputable section

/-- Actual unused entries within the stated radius of their actual mean. -/
def centralExceptionStock {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (reserved : Finset (Cell n)) (radius : ℝ) : Finset (pool n) :=
  (actualUnusedPool a reserved).filter fun v =>
    |centralPoolValue v - centralEntriesMean (actualUnusedPool a reserved) centralPoolValue| ≤ radius

/-- Central values can be installed into all exceptional cells, then the
remaining exact pool can be sorted into a supplied positive regular factor.
The factor is assumed to lie in the unreserved cells. Its existence, the
stock lower bound, and the comparison with the original mean remain separate. -/
theorem place_central_exceptions_and_complete_factor {n k : ℕ}
    (a : Cell n ≃ Fin (n * n)) (reserved E : Finset (Cell n))
    (hE : E ⊆ Finset.univ \ reserved) (hreg : CellFactorRegular E k)
    (hk : 0 < k) (hn : 0 < n)
    (hmain : mainCells n ⊆ reserved) (hanti : antiCells n ⊆ reserved)
    (X radius : ℝ)
    (hwidth : ∀ u ∈ actualUnusedPool a reserved, ∀ v ∈ actualUnusedPool a reserved,
      (u.val : ℝ) - (v.val : ℝ) < X)
    (hstock : ((Finset.univ \ reserved) \ E).card ≤
      (centralExceptionStock a reserved radius).card) :
    ∃ (chosen : Finset (pool n)) (a₁ b : Cell n ≃ Fin (n * n)),
      chosen ⊆ centralExceptionStock a reserved radius ∧
      chosen.card = ((Finset.univ \ reserved) \ E).card ∧
      ((Finset.univ \ reserved) \ E).image (entry a₁) = chosen.image Subtype.val ∧
      (∀ z ∈ reserved, entry a₁ z = entry a z) ∧
      actualUnusedPool a₁ (reserved ∪ ((Finset.univ \ reserved) \ E)) =
        actualUnusedPool a reserved \ chosen ∧
      (∀ z ∈ reserved ∪ ((Finset.univ \ reserved) \ E), entry b z = entry a₁ z) ∧
      (∀ r, |(rowSum b r : ℝ) -
        ((∑ z ∈ rowCells r ∩ (reserved ∪ ((Finset.univ \ reserved) \ E)), (entry a₁ z : ℝ)) +
          (k : ℝ) * centralEntriesMean (actualUnusedPool a reserved \ chosen) centralPoolValue)| < X) ∧
      (∀ c, |(columnSum b c : ℝ) -
        ((∑ z ∈ columnCells c ∩ (reserved ∪ ((Finset.univ \ reserved) \ E)), (entry a₁ z : ℝ)) +
          (k : ℝ) * centralEntriesMean (actualUnusedPool a reserved \ chosen) centralPoolValue)| < X) ∧
      mainSum b = mainSum a ∧ antiSum b = antiSum a ∧
      Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
  classical
  let exc := (Finset.univ \ reserved) \ E
  obtain ⟨chosen, hchosen, hcard⟩ := Finset.exists_subset_card_eq hstock
  have hsub : chosen ⊆ actualUnusedPool a reserved := by
    intro v hv
    exact (Finset.mem_filter.mp (hchosen hv)).1
  have hdisj : Disjoint exc reserved := by
    apply Finset.disjoint_left.mpr
    intro z hz hr
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2 hr
  obtain ⟨a₁, himage, hfixed, _, _⟩ := place_finite_population a exc chosen reserved hcard hdisj
    (fun v hv => actualUnusedPool_avoids a reserved v (hsub hv))
  have hpool := actualUnusedPool_after_placement a a₁ reserved exc chosen hfixed himage
  have hfree : E = Finset.univ \ (reserved ∪ exc) := by
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union, exc]
    constructor
    · intro hz
      have hzfree := Finset.mem_sdiff.mp (hE hz)
      simp [hzfree.2, hz]
    · intro hz
      by_contra he
      exact hz (Or.inr ⟨fun hr => hz (Or.inl hr), he⟩)
  have hwidth₁ : ∀ u ∈ actualUnusedPool a₁ (reserved ∪ exc),
      ∀ v ∈ actualUnusedPool a₁ (reserved ∪ exc), (u.val : ℝ) - (v.val : ℝ) < X := by
    rw [hpool]
    intro u hu v hv
    exact hwidth u (Finset.mem_sdiff.mp hu).1 v (Finset.mem_sdiff.mp hv).1
  obtain ⟨b, hfixb, hrow, hcol, hm, ha, hprimes, hinj⟩ :=
    sorted_regular_factor_completion a₁ (reserved ∪ exc) E hfree hreg hk hn
      (hmain.trans Finset.subset_union_left) (hanti.trans Finset.subset_union_left) X hwidth₁
  have hm₁ : mainSum a₁ = mainSum a := by
    unfold mainSum
    apply Finset.sum_congr rfl
    intro i _
    exact hfixed _ (hmain (by simp))
  have ha₁ : antiSum a₁ = antiSum a := by
    unfold antiSum
    apply Finset.sum_congr rfl
    intro i _
    exact hfixed _ (hanti (by simp))
  refine ⟨chosen, a₁, b, hchosen, hcard, himage, hfixed, hpool, hfixb, ?_, ?_,
    hm.trans hm₁, ha.trans ha₁, hprimes, hinj⟩
  · simpa [hpool] using hrow
  · simpa [hpool] using hcol

end
end Sude
