import Sude.ActiveSupportCenteredInvoice
import Sude.CenteredReferencePairEndpoints

/-! Active-preserving centered reference with same-witness network pair endpoints. -/
namespace Sude
noncomputable section

theorem twoNetworks_centered_invoice_preserves_active_pair_endpoints {n : ℕ} {Er Ec : Type*}
    [Fintype Er] [DecidableEq Er] [Fintype Ec] [DecidableEq Ec]
    (a : Cell n ≃ Fin (n * n)) (reserved active : Finset (Cell n))
    (rows cols : List (LayerPacking.Layer n))
    (hr : LayerPacking.PackedLayers reserved rows)
    (hc : LayerPacking.PackedLayers
      (LayerPacking.transposeCells (reserved ∪ LayerPacking.layersSupport rows)) cols)
    (hrowActive : LayerPacking.layersSupport rows ⊆ active)
    (hcolActive : LayerPacking.transposeCells (LayerPacking.layersSupport cols) ⊆ active)
    (rowGap : Fin rows.length → Fin n → ℕ) (colGap : Fin cols.length → Fin n → ℕ)
    (hrowGap : ∀ i e, entry a ((rows.get i).1 e, (rows.get i).2 e) =
      entry a (e, (rows.get i).2 e) + rowGap i e)
    (hcolGap : ∀ i e, entry a ((cols.get i).2 e, (cols.get i).1 e) =
      entry a ((cols.get i).2 e, e) + colGap i e)
    (BR : CenteredNetwork Er (Fin rows.length × Fin n) (hr.rowPairs a rowGap hrowGap))
    (BC : CenteredNetwork Ec (Fin cols.length × Fin n) (hc.columnPairs a colGap hcolGap)) :
    ∃ b₀ : Cell n ≃ Fin (n * n),
      TwoNetworkReferenceInvoice a b₀ rows cols hr hc rowGap colGap hrowGap hcolGap BR BC ∧
      mainSum b₀ = mainSum a ∧ antiSum b₀ = antiSum a ∧
      (∀ c ∈ reserved, entry b₀ c = entry a c) ∧
      (∀ c ∉ active, entry b₀ c = entry a c) ∧
      (∀ k, entry b₀ (layerPairSlot rows k false) + entry b₀ (layerPairSlot rows k true) =
        entry a (layerPairSlot rows k false) + entry a (layerPairSlot rows k true)) ∧
      (∀ k, entry b₀ (layerPairSlot cols k false).swap + entry b₀ (layerPairSlot cols k true).swap =
        entry a (layerPairSlot cols k false).swap + entry a (layerPairSlot cols k true).swap) ∧
      (∀ k, (entry b₀ (layerPairSlot rows k false) = entry a (layerPairSlot rows k false) ∧
          entry b₀ (layerPairSlot rows k true) = entry a (layerPairSlot rows k true)) ∨
        (entry b₀ (layerPairSlot rows k false) = entry a (layerPairSlot rows k true) ∧
          entry b₀ (layerPairSlot rows k true) = entry a (layerPairSlot rows k false))) ∧
      (∀ k, (entry b₀ (layerPairSlot cols k false).swap = entry a (layerPairSlot cols k false).swap ∧
          entry b₀ (layerPairSlot cols k true).swap = entry a (layerPairSlot cols k true).swap) ∨
        (entry b₀ (layerPairSlot cols k false).swap = entry a (layerPairSlot cols k true).swap ∧
          entry b₀ (layerPairSlot cols k true).swap = entry a (layerPairSlot cols k false).swap)) ∧
      active.image (entry b₀) = active.image (entry a) ∧
      Set.range (entry b₀) = pool n ∧ Function.Injective (entry b₀) ∧
      (∀ tr : Er → ℤ, (∀ e, (2 : ℤ) ∣ tr e) →
        (∀ e, -(evenGridCenter (BR.radius e) : ℤ) ≤ tr e) →
        (∀ e, tr e ≤ evenGridCenter (BR.radius e)) →
        ∀ tc : Ec → ℤ, (∀ e, (2 : ℤ) ∣ tc e) →
        (∀ e, -(evenGridCenter (BC.radius e) : ℤ) ≤ tc e) →
        (∀ e, tc e ≤ evenGridCenter (BC.radius e)) →
        ∃ b : Cell n ≃ Fin (n * n),
          (∀ r, (rowSum b r : ℤ) - (rowSum b₀ r : ℤ) =
            ∑ e : Er, edgeTransfer BR.source BR.target tr e r) ∧
          (∀ c, (columnSum b c : ℤ) - (columnSum b₀ c : ℤ) =
            ∑ e : Ec, edgeTransfer BC.source BC.target tc e c) ∧
          mainSum b = mainSum b₀ ∧ antiSum b = antiSum b₀ ∧
          (∀ c ∈ reserved, entry b c = entry b₀ c) ∧
          (∀ c ∉ active, entry b c = entry a c) ∧
          active.image (entry b) = active.image (entry a) ∧
          Set.range (entry b) = pool n ∧ Function.Injective (entry b)) := by
  classical
  obtain ⟨hr', hc'⟩ := LayerPacking.packed_layers_extend_outside_active
    reserved active rows cols hr hc hrowActive hcolActive
  obtain ⟨Sr₀, Sc₀, b₀, hr₀, hc₀, hrcenters, hccenters, hrows₀, hcols₀,
    hrinvoice, hcinvoice, hmain, hanti, hfixed, hrowPairs, hcolPairs, hrowEndpoints, hcolEndpoints, hrealize⟩ :=
    twoNetworks_centered_transfers_with_invoice_pair_endpoints a (reserved ∪ (Finset.univ \ active))
      rows cols hr' hc' rowGap colGap hrowGap hcolGap BR BC
  have hbaseOutside : ∀ c ∉ active, entry b₀ c = entry a c := by
    intro c hcactive
    exact hfixed c (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hcactive⟩))
  have hbaseImage : active.image (entry b₀) = active.image (entry a) := by
    apply finite_support_value_image_eq active (entry b₀) (entry a)
      (entry_injective b₀) (entry_injective a)
    · exact (entry_range b₀).trans (entry_range a).symm
    · exact hbaseOutside
  refine ⟨b₀, ⟨Sr₀, Sc₀, hr₀, hc₀, hrcenters, hccenters, hrows₀, hcols₀,
    hrinvoice, hcinvoice⟩, hmain, hanti, ?_, hbaseOutside, hrowPairs, hcolPairs, hrowEndpoints, hcolEndpoints, hbaseImage,
    entry_range b₀, entry_injective b₀, ?_⟩
  · intro c hc
    exact hfixed c (Finset.mem_union_left _ hc)
  · intro tr hre hrl hrh tc hce hcl hch
    obtain ⟨b, hrows, hcols, hm, ha, hfixed', hpool, hinj⟩ :=
      hrealize tr hre hrl hrh tc hce hcl hch
    have hnewOutside : ∀ c ∉ active, entry b c = entry a c := by
      intro c hcactive
      exact (hfixed' c (Finset.mem_union_right _ (Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ _, hcactive⟩))).trans (hbaseOutside c hcactive)
    have hnewImage : active.image (entry b) = active.image (entry a) := by
      apply finite_support_value_image_eq active (entry b) (entry a) hinj (entry_injective a)
      · exact hpool.trans (entry_range a).symm
      · exact hnewOutside
    refine ⟨b, hrows, hcols, hm, ha, ?_, hnewOutside, hnewImage, hpool, hinj⟩
    intro c hc
    exact hfixed' c (Finset.mem_union_left _ hc)


end
end Sude
