import Sude.FWGrowthOrdinaryDPAllocation

/-! The ordinary DP reference uses the exact complement of the three
rectangle-label families from the same stage permutation. -/
namespace Sude
noncomputable section

/-- If the three rectangle slot families have the stated label images under
the same trace-stage permutation, the ordinary slot labels are exactly the
stage lows left after removing those three families. The midpoint sum is
therefore also exactly the remaining-label sum. -/
theorem fw_growth_ordinary_label_image_sum {n : ℕ}
    {initial final : Finset ℕ} {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 (6 * (n+8)) initial radius final last stages)
    (ω : Fin stages.length → Equiv.Perm (Fin (6*(n+8))))
    (T U V : Fin stages.length → Finset ℕ)
    (hmap : ∀ j,
      (fwGrowthMainSlots n).image (fun i => trace.lowAt rfl j (ω j i)) = T j ∧
      (fwGrowthAntiSlots n).image (fun i => trace.lowAt rfl j (ω j i)) = U j ∧
      (fwGrowthPartnerSlots n).image (fun i => trace.lowAt rfl j (ω j i)) = V j) :
    ∀ j,
      (fwGrowthOrdinarySlots n).image (fun i => trace.lowAt rfl j (ω j i)) =
        (stages.get j).lows \ ((T j ∪ U j) ∪ V j) ∧
      (∑ i ∈ fwGrowthOrdinarySlots n,
        growthStageMidpoint (stages.get j) (trace.lowAt rfl j (ω j i))) =
      ∑ p ∈ (stages.get j).lows \ ((T j ∪ U j) ∪ V j),
        growthStageMidpoint (stages.get j) p := by
  classical
  intro j
  let f : Fin (6*(n+8)) → ℕ := fun i => trace.lowAt rfl j (ω j i)
  have hf : Function.Injective f := by
    intro i k h
    apply (ω j).injective
    exact ((BTStageTrace.stageAt stages rfl j).lows.orderEmbOfFin
      (trace.stage_properties _ (BTStageTrace.stageAt_mem stages rfl j)).2.2.2.1).injective h
  have hfull : Finset.univ.image f = (stages.get j).lows := by
    have hlo : Finset.univ.image (trace.lowAt rfl j) = (stages.get j).lows := by
      exact Finset.image_orderEmbOfFin_univ _ _
    calc
      _ = (Finset.univ.image (ω j)).image (trace.lowAt rfl j) := by
        rw [Finset.image_image]
        rfl
      _ = _ := by simpa using hlo
  have hsel : (fwGrowthMainSlots n ∪ fwGrowthAntiSlots n ∪ fwGrowthPartnerSlots n).image f =
      (T j ∪ U j) ∪ V j := by
    dsimp [f]
    rw [Finset.image_union, Finset.image_union, (hmap j).1, (hmap j).2.1, (hmap j).2.2]
  have hremaining : (fwGrowthOrdinarySlots n).image f =
      (stages.get j).lows \ ((T j ∪ U j) ∪ V j) := by
    rw [fw_growth_ordinary_slots_eq_complement, Finset.image_sdiff _ _ hf, hfull, hsel]
  refine ⟨hremaining, ?_⟩
  rw [← hremaining, Finset.sum_image (Set.injOn_of_injective hf)]


/-- The original-stage mean used by the ordinary DP assignment is the mean
of that same trace stage's remaining low labels, retaining its occurrence. -/
theorem fw_growth_ordinary_dp_mean {n : ℕ} {initial final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 (6*(n+8)) initial radius final last stages)
    (ω : Fin stages.length → Equiv.Perm (Fin (6*(n+8))))
    (T U V : Fin stages.length → Finset ℕ)
    (hmap : ∀ j, (fwGrowthMainSlots n).image (fun i => trace.lowAt rfl j (ω j i)) = T j ∧
      (fwGrowthAntiSlots n).image (fun i => trace.lowAt rfl j (ω j i)) = U j ∧
      (fwGrowthPartnerSlots n).image (fun i => trace.lowAt rfl j (ω j i)) = V j)
    (j : Fin stages.length) :
    prefixOriginalStageMean (fwGrowthOrdinaryPopulation n stages.length) Prod.fst
      (fun s => growthStageMidpoint (stages.get s.1) (trace.lowAt rfl s.1 (ω s.1 s.2))) j =
    (∑ p ∈ (stages.get j).lows \ ((T j ∪ U j) ∪ V j), growthStageMidpoint (stages.get j) p) /
      (6*n : ℕ) := by
  classical
  let f : Fin (6*(n+8)) → ℕ := fun i => trace.lowAt rfl j (ω j i)
  have hinj : Function.Injective f := by
    intro a b h
    apply (ω j).injective
    exact (Finset.orderEmbOfFin _ _).injective h
  have himage := (fw_growth_ordinary_label_image_sum trace ω T U V hmap j).1
  have hfiber : (fwGrowthOrdinaryPopulation n stages.length).filter (fun s => s.1 = j) =
      ({j} : Finset (Fin stages.length)).product (fwGrowthOrdinarySlots n) := by
    ext ⟨k,i⟩
    simp [fwGrowthOrdinaryPopulation, eq_comm, and_comm]
  unfold prefixOriginalStageMean
  rw [hfiber]
  change (∑ s ∈ ({j} : Finset (Fin stages.length)) ×ˢ fwGrowthOrdinarySlots n,
    growthStageMidpoint (stages.get s.1) (trace.lowAt rfl s.1 (ω s.1 s.2))) /
      ((({j} : Finset (Fin stages.length)) ×ˢ fwGrowthOrdinarySlots n).card : ℝ) = _
  rw [Finset.sum_product, Finset.sum_singleton, Finset.card_product, Finset.card_singleton, one_mul]
  rw [(fw_growth_slot_group_cardinalities n).2.2.2]
  rw [← himage, Finset.sum_image hinj.injOn]

end
end Sude
