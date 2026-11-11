import Sude.FWSeedGrowthBandProducts
import Sude.FixedGapLayerNetworkCancellation

/-! The seed/growth network residual cancels when every remaining layer has
constant gap on the same supplied network. This does not establish those gap
hypotheses for any FW witness. Apply the same result to a supplied
transposed network for the corresponding physical column. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

/-- With exact slot matching and a gap constant within each remaining layer,
the seed/growth correction is zero. The gap may vary from layer to layer. -/
theorem fw_residual_fixed_gap_row_cancellation {n P : ℕ}
    (br sr wr gr : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hsr : sr.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hgr : gr.length = P * 3)
    {a : Cell n ≃ Fin (n*n)}
    (v : RowNetworkPairs (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) a)
    (blocks : (Fin 3 × Fin n) → Finset (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n))
    (hblock : ∀ edge, blocks edge =
      (fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex br sr wr gr hbr hsr hwr hgr ((x,edge.1),edge.2)))
    (g : Fin (((br ++ sr) ++ wr) ++ gr).length → ℕ)
    (hslot : ∀ i ∈ fwSeedJointLayerImage br sr wr gr hsr ∪ fwGrowthJointLayerImage br sr wr gr hgr,
      ∀ e side, rowNetworkSlot v ((i,e),side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) (i,e) side)
    (hgap : ∀ i ∈ fwSeedJointLayerImage br sr wr gr hsr ∪ fwGrowthJointLayerImage br sr wr gr hgr,
      ∀ e, v.gap (i,e) = g i)
    (r : Fin n) :
    (∑ k ∈ (Finset.univ.biUnion blocks) \ (fwBridgeJointPairImage br sr wr gr hbr ∪
      fwWideJointPairImage br sr wr gr hwr), rowNetworkDelta v k r) = 0 := by
  classical
  rw [(fw_joint_network_residual_seed_growth br sr wr gr hbr hsr hwr hgr blocks hblock).1]
  rw [fw_seed_joint_pair_image_product, fw_growth_joint_pair_image_product]
  have hprod : (fwSeedJointLayerImage br sr wr gr hsr).product (Finset.univ : Finset (Fin n)) ∪
      (fwGrowthJointLayerImage br sr wr gr hgr).product (Finset.univ : Finset (Fin n)) =
      (fwSeedJointLayerImage br sr wr gr hsr ∪ fwGrowthJointLayerImage br sr wr gr hgr).product Finset.univ := by
    ext ⟨i,e⟩
    simp
  rw [hprod]
  exact row_network_fixed_gap_layers_sum_zero (((br ++ sr) ++ wr) ++ gr) v _ g hslot hgap r

/-- Real-cast version for midpoint identities. -/
theorem fw_residual_fixed_gap_row_cancellation_real {n P : ℕ}
    (br sr wr gr : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hsr : sr.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hgr : gr.length = P * 3)
    {a : Cell n ≃ Fin (n*n)}
    (v : RowNetworkPairs (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) a)
    (blocks : (Fin 3 × Fin n) → Finset (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n))
    (hblock : ∀ edge, blocks edge =
      (fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex br sr wr gr hbr hsr hwr hgr ((x,edge.1),edge.2)))
    (g : Fin (((br ++ sr) ++ wr) ++ gr).length → ℕ)
    (hslot : ∀ i ∈ fwSeedJointLayerImage br sr wr gr hsr ∪ fwGrowthJointLayerImage br sr wr gr hgr,
      ∀ e side, rowNetworkSlot v ((i,e),side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) (i,e) side)
    (hgap : ∀ i ∈ fwSeedJointLayerImage br sr wr gr hsr ∪ fwGrowthJointLayerImage br sr wr gr hgr,
      ∀ e, v.gap (i,e) = g i)
    (r : Fin n) :
    (∑ k ∈ (Finset.univ.biUnion blocks) \ (fwBridgeJointPairImage br sr wr gr hbr ∪
      fwWideJointPairImage br sr wr gr hwr), (rowNetworkDelta v k r : ℝ)) = 0 := by
  exact_mod_cast fw_residual_fixed_gap_row_cancellation br sr wr gr hbr hsr hwr hgr v blocks hblock g hslot hgap r

end
end Sude
