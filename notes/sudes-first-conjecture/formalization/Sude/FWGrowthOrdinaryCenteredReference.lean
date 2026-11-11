import Sude.FWGrowthOrdinaryDPAllocation

/-! Exact conversion between a centered ordinary growth-pair sum and the
ordinary midpoint sum minus its original-stage reference. -/
namespace Sude
noncomputable section

/-- If each stage has ordinary weight twelve, its weighted original-stage
means sum to `12 * ∑ μ`. This is a finite-sum identity, not a line bound. -/
theorem fw_growth_ordinary_centered_reference {n P : ℕ} (hn : 0 < n)
    (w midpoint : Fin P × Fin (6*(n+8)) → ℝ) (μ : Fin P → ℝ)
    (hmass : ∀ j : Fin P,
      (∑ s ∈ (fwGrowthOrdinaryPopulation n P).filter (fun s => s.1 = j), w s) = 12) :
    (∑ s : {s // s ∈ fwGrowthOrdinaryPopulation n P},
      w s.val * (midpoint s.val - μ s.val.1)) =
    (∑ s : {s // s ∈ fwGrowthOrdinaryPopulation n P}, w s.val * midpoint s.val) -
      12 * ∑ j, μ j := by
  classical
  let pop := fwGrowthOrdinaryPopulation n P
  have hstage : pop.image Prod.fst = Finset.univ := by
    have hne : (fwGrowthOrdinarySlots n).Nonempty := by
      apply Finset.card_pos.mp
      rw [(fw_growth_slot_group_cardinalities n).2.2.2]
      omega
    obtain ⟨i, hi⟩ := hne
    ext j
    simp only [Finset.mem_univ, iff_true]
    exact Finset.mem_image.mpr ⟨(j,i), by simp [pop, fwGrowthOrdinaryPopulation, hi], rfl⟩
  have href : (∑ s : {s // s ∈ pop}, w s.val * μ s.val.1) = 12 * ∑ j, μ j := by
    have hc : (∑ s : {s // s ∈ pop}, w s.val * μ s.val.1) =
        ∑ s ∈ pop, w s * μ s.1 := Finset.sum_coe_sort pop (fun s => w s * μ s.1)
    rw [hc]
    have hg := Finset.sum_fiberwise_of_maps_to
      (s := pop) (t := pop.image Prod.fst) (g := Prod.fst)
      (fun s hs => Finset.mem_image_of_mem Prod.fst hs) (fun s => w s * μ s.1)
    rw [← hg, hstage, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← hmass j, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s hs
    have hsj := (Finset.mem_filter.mp hs).2
    rw [hsj]
  change (∑ s : {s // s ∈ pop}, w s.val * (midpoint s.val - μ s.val.1)) = _
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [href]

end
end Sude
