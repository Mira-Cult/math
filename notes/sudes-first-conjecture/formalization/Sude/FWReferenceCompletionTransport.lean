import Sude.ReferenceCompletionEntryInputs
import Sude.FWRoleSupportForNetworks

/-! Same-reference completion transport for supplied FW geometry. The old
reference invoices and a completed square fixing the full reservation are
inputs; no completion, numeric gate, prime diagonals or later flow is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

/-- Rebase the actual FW row and column networks after a completion that fixes
the complete reservation, retaining both original invoice bounds and both
diagonal sums on one synchronized reference. -/
theorem fw_reference_completion_transport {n P : ℕ} (hP : P ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n) (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc))
    (a b c : Cell n ≃ Fin (n*n))
    (vr : RowNetworkPairs (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) a)
    (vc : RowNetworkPairs (Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n) (LayerPacking.transposePlacement a))
    (BR : CenteredNetwork (Fin 3 × Fin n) _ vr) (BC : CenteredNetwork (Fin 3 × Fin n) _ vc)
    (hslotr : ∀ t side, rowNetworkSlot vr (t,side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) t side)
    (hslotc : ∀ t side, rowNetworkSlot vc (t,side) = layerPairSlot (((bc ++ sc) ++ wc) ++ gc) t side)
    (roles : Finset (Cell n))
    (hroles : roles = fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc))
    (hfixed : ∀ x ∈ packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc)), entry c x = entry a x)
    (hoffactive : ∀ x ∉ roles, entry b x = entry a x)
    (himage : roles.image (entry b) = roles.image (entry a))
    (hmain : mainSum b = mainSum a) (hanti : antiSum b = antiSum a)
    (hinvrow : ∀ r, |2 * (rowSum b r : ℤ) - physicalNetworkMidpointTwice vr BR r| ≤ 9)
    (hinvcol : ∀ j, |2 * (columnSum b j : ℤ) - physicalNetworkMidpointTwice vc BC j| ≤ 9) :
    ∃ d : Cell n ≃ Fin (n*n),
      (∀ x ∈ roles, entry d x = entry b x) ∧ (∀ x ∉ roles, entry d x = entry c x) ∧
      mainSum d = mainSum c ∧ antiSum d = antiSum c ∧
      ∃ hr : ∀ k side, entry c (rowNetworkSlot vr (k,side)) = entry a (rowNetworkSlot vr (k,side)),
      ∃ hc : ∀ k side, entry (LayerPacking.transposePlacement c) (rowNetworkSlot vc (k,side)) =
          entry (LayerPacking.transposePlacement a) (rowNetworkSlot vc (k,side)),
        (∀ r, |2 * (rowSum d r : ℤ) - physicalNetworkMidpointTwice (rowNetworkPairsRebase vr c hr)
            (centeredNetworkRebase vr BR c hr) r| ≤ 9) ∧
        (∀ j, |2 * (columnSum d j : ℤ) - physicalNetworkMidpointTwice
          (rowNetworkPairsRebase vc (LayerPacking.transposePlacement c) hc)
            (centeredNetworkRebase vc BC (LayerPacking.transposePlacement c) hc) j| ≤ 9) := by
  classical
  have hg := fw_role_support_for_trace_networks hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
  dsimp only at hg
  rw [← hroles] at hg
  have hca : ∀ x ∈ roles, entry c x = entry a x := fun x hx => hfixed x (hg.2.2.1 hx)
  have hrs : ∀ t side, rowNetworkSlot vr (t,side) ∈ roles := by
    intro t side
    rw [hslotr]
    exact hg.1 (layerPairSlot_mem _ t side)
  have hcs : ∀ t side, (rowNetworkSlot vc (t,side)).swap ∈ roles := by
    intro t side
    rw [hslotc]
    exact hg.2.1 (transposedLayerPairSlot_mem _ t side)
  obtain ⟨d, hd, hdo, hr, hc, hrow, hcol⟩ := physical_reference_completion_both_invoices a b c roles vr BR vc BC
    hca hoffactive himage hrs hcs
  have hdiag := reference_completion_diagonal_sums a b c d roles hca hd hoffactive hdo
  refine ⟨d, hd, hdo, hdiag.1 hmain, hdiag.2 hanti, hr, hc, ?_, ?_⟩
  · intro r
    rw [hrow r]
    exact hinvrow r
  · intro j
    rw [hcol j]
    exact hinvcol j

end
end Sude
