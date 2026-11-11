import Sude.FWGrowthPrefixGlobalSelection
import Sude.FWGrowthDiagonalSlots
import Sude.BTGrowthFamilyPlacement

/-! Jointly select and physically allocate the three growth rectangle
families on one trace-placed exact-pool square. -/
namespace Sude
noncomputable section
set_option maxHeartbeats 2000000

/-- Realize the PD3--PD6 growth selections in the designated 12/12/24
pair-index groups on one square. The trace's pair gaps, per-stage endpoint
sets, and every non-growth cell are preserved. Diagonal line estimates and
ordinary-slot balancing are separate obligations. -/
theorem fw_growth_three_family_allocation {n L : ℕ} {initial final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 (6*(n+8)) initial radius final last stages)
    (hpool : ∀ p ∈ initial, p ∈ pool n) (hn : 3 ≤ n)
    (X : ℝ) (hX : 0 ≤ X) (hnarrow : NarrowedStages (X/6) stages)
    (offset : ℕ) (hoff : offset + stages.length*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = stages.length*3) (hc : cols.length = stages.length*3)
    (a : Cell n ≃ Fin (n*n))
    (hplaced : ∀ x : PrefixPhysicalInputs stages.length 6 3 n,
      entry a (btGrowingOffsetCells offset hoff hs choice rows cols hr hc x) =
        (trace.poolValues rfl hpool (prefixPhysicalInput (by omega) (by omega) x)).val) :
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice rows cols hr hc
    ∃ (T U V : Fin stages.length → Finset ℕ)
      (ω : Fin stages.length → Equiv.Perm (Fin (6*(n+8)))) (a' : Cell n ≃ Fin (n*n)),
      (∀ j, T j ⊆ (stages.get j).lows ∧ U j ⊆ (stages.get j).lows \ T j ∧
        V j ⊆ (stages.get j).lows \ (T j ∪ U j) ∧
        (T j).card = 12 ∧ (U j).card = 12 ∧ (V j).card = 24) ∧
      (∀ j, (fwGrowthMainSlots n).image (fun i => trace.lowAt rfl j (ω j i)) = T j ∧
        (fwGrowthAntiSlots n).image (fun i => trace.lowAt rfl j (ω j i)) = U j ∧
        (fwGrowthPartnerSlots n).image (fun i => trace.lowAt rfl j (ω j i)) = V j) ∧
      (∀ x, entry a' (cells x) = (trace.poolValues rfl hpool (stagePairPermutation ω x)).val) ∧
      (∀ c, c ∉ Set.range cells → entry a' c = entry a c) ∧
      (∀ j, Finset.univ.image (fun x : Fin (6*(n+8)) × Bool => entry a' (cells ((j,x.1),x.2))) =
        Finset.univ.image (fun x : Fin (6*(n+8)) × Bool => entry a (cells ((j,x.1),x.2)))) ∧
      (∀ j i, entry a' (cells ((j,i),true)) =
        entry a' (cells ((j,i),false)) + (stages.get j).gap) ∧
      let μ := fun j => (∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) /
        (6 * (n+8) : ℕ)
      let E1 := (∑ j, ∑ p ∈ T j, growthStageMidpoint (stages.get j) p) - (12 : ℝ) * ∑ j, μ j
      let D2 := (∑ j, ∑ p ∈ U j, growthStageMidpoint (stages.get j) p) - (12 : ℝ) * ∑ j, μ j
      let E2 := (∑ j, ∑ p ∈ T j ∪ U j, growthStageMidpoint (stages.get j) p) - (24 : ℝ) * ∑ j, μ j
      let E3 := (∑ j, ∑ p ∈ (T j ∪ U j) ∪ V j, growthStageMidpoint (stages.get j) p) - (48 : ℝ) * ∑ j, μ j
      |E1| ≤ (X/6)/2 ∧ |D2| ≤ ((n+8 : ℝ)/(2*(n+6)))*(X/6) ∧
        |E2| ≤ ((n+5 : ℝ)/(n+6))*(X/6) ∧ |E3| ≤ (3/2:ℝ)*(X/6) ∧
        (0 < X/6 → |E3| < (3/2:ℝ)*(X/6)) := by
  classical
  dsimp only
  obtain ⟨T, U, V, hsel, hbudget⟩ := fw_growth_three_global_selections trace hn X hX hnarrow
  let S : Fin stages.length → Fin 3 → Finset (Fin (6*(n+8))) :=
    fun _ => ![fwGrowthMainSlots n, fwGrowthAntiSlots n, fwGrowthPartnerSlots n]
  let F : Fin stages.length → Fin 3 → Finset ℕ := fun j => ![T j, U j, V j]
  have hsub : ∀ j t, F j t ⊆ (BTStageTrace.stageAt stages rfl j).lows := by
    intro j t
    have hv : V j ⊆ (stages.get j).lows := (hsel j).2.2.1.trans Finset.sdiff_subset
    have hu : U j ⊆ (stages.get j).lows := (hsel j).2.1.trans Finset.sdiff_subset
    fin_cases t
    · simpa [F, BTStageTrace.stageAt] using (hsel j).1
    · simpa [F, BTStageTrace.stageAt] using hu
    · simpa [F, BTStageTrace.stageAt] using hv
  have hT : ∀ j t u, t ≠ u → Disjoint (F j t) (F j u) := by
    intro j t u hne
    have htu : Disjoint (T j) (U j) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      exact (Finset.mem_sdiff.mp ((hsel j).2.1 hy)).2 hx
    have htv : Disjoint (T j) (V j) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      exact (Finset.mem_sdiff.mp ((hsel j).2.2.1 hy)).2 (Finset.mem_union_left _ hx)
    have huv : Disjoint (U j) (V j) := by
      apply Finset.disjoint_left.mpr
      intro x hx hy
      exact (Finset.mem_sdiff.mp ((hsel j).2.2.1 hy)).2 (Finset.mem_union_right _ hx)
    fin_cases t <;> fin_cases u
    all_goals first
      | exact False.elim (hne rfl)
      | simpa [F] using htu
      | simpa [F] using htv
      | simpa [F] using huv
      | simpa [F] using htu.symm
      | simpa [F] using htv.symm
      | simpa [F] using huv.symm
  have hS : ∀ j t u, t ≠ u → Disjoint (S j t) (S j u) := by
    intro j t u hne
    have hd := fw_growth_slot_groups_disjoint n
    fin_cases t <;> fin_cases u
    · exact False.elim (hne rfl)
    · exact hd.1
    · exact hd.2.1
    · exact hd.1.symm
    · exact False.elim (hne rfl)
    · exact hd.2.2.1
    · exact hd.2.1.symm
    · exact hd.2.2.1.symm
    · exact False.elim (hne rfl)
  have hcard : ∀ j t, (S j t).card = (F j t).card := by
    intro j t
    have hc := fw_growth_slot_group_cardinalities n
    have hj := hsel j
    fin_cases t
    · change (fwGrowthMainSlots n).card = (T j).card
      rw [hc.1, (hsel j).2.2.2.1]
    · change (fwGrowthAntiSlots n).card = (U j).card
      rw [hc.2.1, (hsel j).2.2.2.2.1]
    · change (fwGrowthPartnerSlots n).card = (V j).card
      rw [hc.2.2.1, (hsel j).2.2.2.2.2]
  obtain ⟨ω, a', hmap, hperm, hphys, hfix, hstage, hgap⟩ := bt_growth_family_placement
    trace rfl hpool (by omega) (by omega) (by omega) offset hoff hs choice rows cols hr hc a hplaced
    S F hsub hS hT hcard
  refine ⟨T, U, V, ω, a', hsel, ?_, hperm, hfix, hstage, ?_, hbudget⟩
  · intro j
    exact ⟨hmap j 0, hmap j 1, hmap j 2⟩
  · exact hgap

end
end Sude
