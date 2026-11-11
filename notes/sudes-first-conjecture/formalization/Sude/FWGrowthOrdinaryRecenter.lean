import Sude.FWGrowthOrdinaryMeanBridge
import Sude.FWGrowthRemainingMeanCorrection

/-! Recenter the ordinary DP reference using the same selected growth labels.
The twelve-per-stage line weight is supplied, not inferred here. -/
namespace Sude
noncomputable section

/-- If a line has ordinary slot weight twelve in every stage, the difference
between its ordinary DP baseline and the original-stage reference is at most
`3*C/n`, provided the removed-label discrepancy satisfies PD6. The exact
three family images and all assumptions refer to the same trace/permutation. -/
theorem fw_growth_ordinary_dp_reference_recenter {n : ℕ} (hn : 0 < n)
    {initial final : Finset ℕ} {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 (6*(n+8)) initial radius final last stages)
    (ω : Fin stages.length → Equiv.Perm (Fin (6*(n+8))))
    (T U V : Fin stages.length → Finset ℕ) (C : ℝ)
    (hmap : ∀ j, (fwGrowthMainSlots n).image (fun i => trace.lowAt rfl j (ω j i)) = T j ∧
      (fwGrowthAntiSlots n).image (fun i => trace.lowAt rfl j (ω j i)) = U j ∧
      (fwGrowthPartnerSlots n).image (fun i => trace.lowAt rfl j (ω j i)) = V j)
    (hsub : ∀ j, ((T j ∪ U j) ∪ V j) ⊆ (stages.get j).lows)
    (hcard : ∀ j, ((T j ∪ U j) ∪ V j).card = 48)
    (hE : |(∑ j, ∑ p ∈ ((T j ∪ U j) ∪ V j), growthStageMidpoint (stages.get j) p) -
      (48 : ℝ) * ∑ j, ((∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) /
        (6*(n+8) : ℕ))| ≤ (3/2:ℝ)*C)
    (w : (Fin stages.length × Fin (6*(n+8))) → ℝ)
    (hmass : ∀ j, (∑ s ∈ (fwGrowthOrdinaryPopulation n stages.length).filter
      (fun s => s.1 = j), w s) = 12) :
    |(∑ j ∈ (fwGrowthOrdinaryPopulation n stages.length).image Prod.fst,
      (∑ s ∈ (fwGrowthOrdinaryPopulation n stages.length).filter (fun s => s.1 = j), w s) *
        prefixOriginalStageMean (fwGrowthOrdinaryPopulation n stages.length) Prod.fst
          (fun s => growthStageMidpoint (stages.get s.1) (trace.lowAt rfl s.1 (ω s.1 s.2))) j) -
      12 * ∑ j, ((∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) /
        (6*(n+8) : ℕ))| ≤ 3*C/(n : ℝ) := by
  classical
  let A : Fin stages.length → Finset ℕ := fun j => (stages.get j).lows
  let R : Fin stages.length → Finset ℕ := fun j => (T j ∪ U j) ∪ V j
  let v : Fin stages.length → ℕ → ℝ := fun j p => growthStageMidpoint (stages.get j) p
  let pop := fwGrowthOrdinaryPopulation n stages.length
  let midpoint : (Fin stages.length × Fin (6*(n+8))) → ℝ := fun s =>
    growthStageMidpoint (stages.get s.1) (trace.lowAt rfl s.1 (ω s.1 s.2))
  have hA : ∀ j, (A j).card = 6*(n+8) := by
    intro j
    exact (trace.stage_properties _ (List.get_mem _ _)).2.2.2.1
  have hν : ∀ j, prefixOriginalStageMean pop Prod.fst midpoint j =
      (∑ p ∈ A j \ R j, v j p) / (6*n : ℕ) := by
    intro j
    exact fw_growth_ordinary_dp_mean trace ω T U V hmap j
  have hstage : pop.image Prod.fst = Finset.univ := by
    have hnonempty : (fwGrowthOrdinarySlots n).Nonempty := by
      apply Finset.card_pos.mp
      rw [(fw_growth_slot_group_cardinalities n).2.2.2]
      omega
    obtain ⟨i, hi⟩ := hnonempty
    ext j
    simp only [Finset.mem_univ, iff_true]
    exact Finset.mem_image.mpr ⟨(j,i), by simp [pop, fwGrowthOrdinaryPopulation, hi], rfl⟩
  have hbound := fw_growth_twelve_weight_mean_shift_bound n hn A R v C hA hsub hcard hE
  have href : (∑ j ∈ pop.image Prod.fst,
      (∑ s ∈ pop.filter (fun s => s.1 = j), w s) * prefixOriginalStageMean pop Prod.fst midpoint j) -
      12 * ∑ j, ((∑ p ∈ A j, v j p) / (6*(n+8) : ℕ)) =
      12 * ∑ j, ((∑ p ∈ A j \ R j, v j p) / (6*n : ℕ) -
        (∑ p ∈ A j, v j p) / (6*(n+8) : ℕ)) := by
    rw [hstage, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hmass j, hν j]
    ring
  change |(∑ j ∈ pop.image Prod.fst,
      (∑ s ∈ pop.filter (fun s => s.1 = j), w s) * prefixOriginalStageMean pop Prod.fst midpoint j) -
      12 * ∑ j, ((∑ p ∈ A j, v j p) / (6*(n+8) : ℕ))| ≤ 3*C/(n : ℝ)
  rw [href]
  exact hbound

end
end Sude
