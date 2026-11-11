import Sude.FamilyGrid
import Sude.TwoNetworkSwitchPairSums

/-! The same centered network reference retains every physical pair sum. -/
namespace Sude
noncomputable section

theorem twoNetworks_centered_transfers_with_invoice_pair_sums {n : ℕ} {Er Ec : Type*}
    [Fintype Er] [DecidableEq Er] [Fintype Ec] [DecidableEq Ec]
    (a : Cell n ≃ Fin (n * n)) (reserved : Finset (Cell n))
    (rows cols : List (LayerPacking.Layer n))
    (hr : LayerPacking.PackedLayers reserved rows)
    (hc : LayerPacking.PackedLayers
      (LayerPacking.transposeCells (reserved ∪ LayerPacking.layersSupport rows)) cols)
    (rowGap : Fin rows.length → Fin n → ℕ)
    (colGap : Fin cols.length → Fin n → ℕ)
    (hrowGap : ∀ i e, entry a ((rows.get i).1 e, (rows.get i).2 e) =
      entry a (e, (rows.get i).2 e) + rowGap i e)
    (hcolGap : ∀ i e, entry a ((cols.get i).2 e, (cols.get i).1 e) =
      entry a ((cols.get i).2 e, e) + colGap i e)
    (BR : CenteredNetwork Er (Fin rows.length × Fin n) (hr.rowPairs a rowGap hrowGap))
    (BC : CenteredNetwork Ec (Fin cols.length × Fin n) (hc.columnPairs a colGap hcolGap)) :
    ∃ (Sr₀ : Finset (Fin rows.length × Fin n)) (Sc₀ : Finset (Fin cols.length × Fin n))
      (b₀ : Cell n ≃ Fin (n * n)),
      Sr₀ ⊆ Finset.univ.biUnion BR.block ∧ Sc₀ ⊆ Finset.univ.biUnion BC.block ∧
      (∀ e, ((∑ k ∈ Sr₀ ∩ BR.block e, rowGap k.1 k.2 : ℕ) : ℤ) = evenGridCenter (BR.radius e)) ∧
      (∀ e, ((∑ k ∈ Sc₀ ∩ BC.block e, colGap k.1 k.2 : ℕ) : ℤ) = evenGridCenter (BC.radius e)) ∧
      (∀ r, (rowSum b₀ r : ℤ) - (rowSum a r : ℤ) = ∑ k ∈ Sr₀, layerTransfer rows rowGap k r) ∧
      (∀ c, (columnSum b₀ c : ℤ) - (columnSum a c : ℤ) = ∑ k ∈ Sc₀, layerTransfer cols colGap k c) ∧
      (∀ r, (rowSum b₀ r : ℤ) - (rowSum a r : ℤ) =
        ∑ e : Er, edgeTransfer BR.source BR.target (fun e => evenGridCenter (BR.radius e)) e r) ∧
      (∀ c, (columnSum b₀ c : ℤ) - (columnSum a c : ℤ) =
        ∑ e : Ec, edgeTransfer BC.source BC.target (fun e => evenGridCenter (BC.radius e)) e c) ∧
      mainSum b₀ = mainSum a ∧ antiSum b₀ = antiSum a ∧
      (∀ c ∈ reserved, entry b₀ c = entry a c) ∧
      (∀ k, entry b₀ (layerPairSlot rows k false) + entry b₀ (layerPairSlot rows k true) =
        entry a (layerPairSlot rows k false) + entry a (layerPairSlot rows k true)) ∧
      (∀ k, entry b₀ (layerPairSlot cols k false).swap + entry b₀ (layerPairSlot cols k true).swap =
        entry a (layerPairSlot cols k false).swap + entry a (layerPairSlot cols k true).swap) ∧
      (∀ tr : Er → ℤ, (∀ e, (2 : ℤ) ∣ tr e) →
        (∀ e, -(evenGridCenter (BR.radius e) : ℤ) ≤ tr e) →
        (∀ e, tr e ≤ evenGridCenter (BR.radius e)) →
        ∀ tc : Ec → ℤ, (∀ e, (2 : ℤ) ∣ tc e) →
        (∀ e, -(evenGridCenter (BC.radius e) : ℤ) ≤ tc e) →
        (∀ e, tc e ≤ evenGridCenter (BC.radius e)) →
        ∃ b : Cell n ≃ Fin (n * n),
          (∀ r, (rowSum b r : ℤ) - (rowSum b₀ r : ℤ) = ∑ e : Er, edgeTransfer BR.source BR.target tr e r) ∧
          (∀ c, (columnSum b c : ℤ) - (columnSum b₀ c : ℤ) = ∑ e : Ec, edgeTransfer BC.source BC.target tc e c) ∧
          mainSum b = mainSum b₀ ∧ antiSum b = antiSum b₀ ∧
          (∀ c ∈ reserved, entry b c = entry b₀ c) ∧
          Set.range (entry b) = pool n ∧ Function.Injective (entry b)) := by
  let vr := hr.rowPairs a rowGap hrowGap
  let vc := hc.columnPairs a colGap hcolGap
  obtain ⟨Sr₀, hr₀, hrcenters, hrchoose⟩ :=
    simultaneous_centered_subsets BR.block vr.gap BR.radius BR.disjoint BR.grid
  obtain ⟨Sc₀, hc₀, hccenters, hcchoose⟩ :=
    simultaneous_centered_subsets BC.block vc.gap BC.radius BC.disjoint BC.grid
  obtain ⟨b₀, hbaseRows, hbaseCols, hbaseMain, hbaseAnti, hbaseFixed, _, _, hrowPairs, hcolPairs⟩ :=
    toggle_two_installed_networks_preserves_pair_sums a reserved rows cols hr hc rowGap colGap hrowGap hcolGap Sr₀ Sc₀
  have hrinvoice (r : Fin n) : (rowSum b₀ r : ℤ) - (rowSum a r : ℤ) =
      ∑ e : Er, edgeTransfer BR.source BR.target (fun e => evenGridCenter (BR.radius e)) e r := by
    rw [hbaseRows r]
    have hsum := rowNetwork_sum_by_reservoir vr BR.block BR.source BR.target
      BR.disjoint BR.endpoints Sr₀ hr₀ r
    change (∑ k ∈ Sr₀, layerTransfer rows rowGap k r) = _ at hsum
    rw [hsum]
    apply Finset.sum_congr rfl
    intro e he
    have hcenter : (∑ k ∈ Sr₀ ∩ BR.block e, (vr.gap k : ℤ)) = evenGridCenter (BR.radius e) := by
      exact_mod_cast hrcenters e
    simp only [hcenter, edgeTransfer]
  have hcinvoice (c : Fin n) : (columnSum b₀ c : ℤ) - (columnSum a c : ℤ) =
      ∑ e : Ec, edgeTransfer BC.source BC.target (fun e => evenGridCenter (BC.radius e)) e c := by
    rw [hbaseCols c]
    have hsum := rowNetwork_sum_by_reservoir vc BC.block BC.source BC.target
      BC.disjoint BC.endpoints Sc₀ hc₀ c
    change (∑ k ∈ Sc₀, layerTransfer cols colGap k c) = _ at hsum
    rw [hsum]
    apply Finset.sum_congr rfl
    intro e he
    have hcenter : (∑ k ∈ Sc₀ ∩ BC.block e, (vc.gap k : ℤ)) = evenGridCenter (BC.radius e) := by
      exact_mod_cast hccenters e
    simp only [hcenter, edgeTransfer]
  refine ⟨Sr₀, Sc₀, b₀, hr₀, hc₀, hrcenters, hccenters, hbaseRows, hbaseCols,
    hrinvoice, hcinvoice, hbaseMain, hbaseAnti, hbaseFixed, hrowPairs, hcolPairs, ?_⟩
  intro tr hre hrl hrh tc hce hcl hch
  obtain ⟨Sr, hrs, hrsums⟩ := hrchoose tr hre hrl hrh
  obtain ⟨Sc, hcs, hcsums⟩ := hcchoose tc hce hcl hch
  obtain ⟨b, hrows, hcols, hm, ha, hfixed, hpool, hinj⟩ :=
    toggle_two_installed_networks a reserved rows cols hr hc rowGap colGap hrowGap hcolGap Sr Sc
  have hrsumsZ : ∀ e, (∑ k ∈ Sr ∩ BR.block e, (vr.gap k : ℤ)) -
      (∑ k ∈ Sr₀ ∩ BR.block e, (vr.gap k : ℤ)) = tr e := by
    intro e
    exact_mod_cast hrsums e
  have hcsumsZ : ∀ e, (∑ k ∈ Sc ∩ BC.block e, (vc.gap k : ℤ)) -
      (∑ k ∈ Sc₀ ∩ BC.block e, (vc.gap k : ℤ)) = tc e := by
    intro e
    exact_mod_cast hcsums e
  refine ⟨b, ?_, ?_, hm.trans hbaseMain.symm, ha.trans hbaseAnti.symm, ?_, hpool, hinj⟩
  · intro r
    have hdiff := rowNetwork_subset_difference vr BR.block BR.source BR.target
      BR.disjoint BR.endpoints Sr Sr₀ hrs hr₀ tr hrsumsZ r
    have hnew := hrows r
    have hbase := hbaseRows r
    change (∑ k ∈ Sr, layerTransfer rows rowGap k r) -
      (∑ k ∈ Sr₀, layerTransfer rows rowGap k r) = _ at hdiff
    omega
  · intro c
    have hdiff := rowNetwork_subset_difference vc BC.block BC.source BC.target
      BC.disjoint BC.endpoints Sc Sc₀ hcs hc₀ tc hcsumsZ c
    have hnew := hcols c
    have hbase := hbaseCols c
    change (∑ k ∈ Sc, layerTransfer cols colGap k c) -
      (∑ k ∈ Sc₀, layerTransfer cols colGap k c) = _ at hdiff
    omega
  · intro c hc'
    exact (hfixed c hc').trans (hbaseFixed c hc').symm


end
end Sude
