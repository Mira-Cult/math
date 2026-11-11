import Sude.FWThetaAllFamilyMidpointReference

/-! The network part of a selected theta witness. All geometry, the ordered
square, the old reference and the permutations are supplied as parameters so
that the same objects can be shared with the family placement witness. This
record does not assert that such a witness exists or assume a completion. -/
namespace Sude
noncomputable section

/-- Network data and reference facts for the exact supplied theta geometry.
The bounded-flow clause keeps natural-number division before the cast to `ℤ`. -/
structure FWThetaNetworkWitness
    (n P : ℕ)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hseedrect : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc))
    (p : Fin 3 → Equiv.Perm (Fin n))
    (ordered oldReference : Cell n ≃ Fin (n*n))
    (roles : Finset (Cell n)) where
  roles_eq : roles = fwGrowthEarlyRoleCells hrect hseedrect hwide hs choice br bc hbr hbc
      sr sc hsr hsc wr wc hwr hwc ∪
    Finset.univ.image (btGrowingOffsetCells
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6))
      hoff hs choice gr gc hgr hgc)
  row_gap : ∀ i e,
    entry ordered (((((br ++ sr) ++ wr) ++ gr).get i).1 e, ((((br ++ sr) ++ wr) ++ gr).get i).2 e) =
      entry ordered (e, ((((br ++ sr) ++ wr) ++ gr).get i).2 e) +
        fwPhysicalRowLayerGap ordered (((br ++ sr) ++ wr) ++ gr) i e
  col_gap : ∀ i e,
    entry ordered (((((bc ++ sc) ++ wc) ++ gc).get i).2 e, ((((bc ++ sc) ++ wc) ++ gc).get i).1 e) =
      entry ordered (((((bc ++ sc) ++ wc) ++ gc).get i).2 e, e) +
        fwPhysicalColumnLayerGap ordered (((bc ++ sc) ++ wc) ++ gc) i e
  row_network : CenteredNetwork (Fin 3 × Fin n) (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n)
    (hrows.rowPairs ordered (fwPhysicalRowLayerGap ordered (((br ++ sr) ++ wr) ++ gr)) row_gap)
  col_network : CenteredNetwork (Fin 3 × Fin n) (Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n)
    (hcols.columnPairs ordered (fwPhysicalColumnLayerGap ordered (((bc ++ sc) ++ wc) ++ gc)) col_gap)
  endpoints : ∀ edge, row_network.source edge = edge.2 ∧ col_network.source edge = edge.2 ∧
    row_network.target edge = p edge.1 edge.2 ∧ col_network.target edge = p edge.1 edge.2
  row_blocks : ∀ edge, row_network.block edge =
    (fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))).attach.image
      (fun x => fwJointActualGridPairIndex br sr wr gr hbr hsr hwr hgr ((x,edge.1),edge.2))
  col_blocks : ∀ edge, col_network.block edge =
    (fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))).attach.image
      (fun x => fwJointActualGridPairIndex bc sc wc gc hbc hsc hwc hgc ((x,edge.1),edge.2))
  invoice : TwoNetworkReferenceInvoice ordered oldReference
    (((br ++ sr) ++ wr) ++ gr) (((bc ++ sc) ++ wc) ++ gc) hrows hcols
    (fwPhysicalRowLayerGap ordered (((br ++ sr) ++ wr) ++ gr))
    (fwPhysicalColumnLayerGap ordered (((bc ++ sc) ++ wc) ++ gc))
    row_gap col_gap row_network col_network
  row_midpoint : ∀ r,
    |2 * (rowSum oldReference r : ℤ) -
      physicalNetworkMidpointTwice
        (hrows.rowPairs ordered (fwPhysicalRowLayerGap ordered (((br ++ sr) ++ wr) ++ gr)) row_gap)
        row_network r| ≤ 9
  col_midpoint : ∀ c,
    |2 * (columnSum oldReference c : ℤ) -
      physicalNetworkMidpointTwice
        (hcols.columnPairs ordered (fwPhysicalColumnLayerGap ordered (((bc ++ sc) ++ wc) ++ gc)) col_gap)
        col_network c| ≤ 9
  main_eq : mainSum oldReference = mainSum ordered
  anti_eq : antiSum oldReference = antiSum ordered
  rectangle_fixed : ∀ c ∈ packedRectangleSupport hs choice, entry oldReference c = entry ordered c
  off_roles : ∀ c ∉ roles, entry oldReference c = entry ordered c
  roles_image : roles.image (entry oldReference) = roles.image (entry ordered)
  old_pool : Set.range (entry oldReference) = pool n
  old_injective : Function.Injective (entry oldReference)
  flows : ∀ fr : Fin 3 × Fin n → ℤ,
    (∀ e, -((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ) ≤ fr e ∧
      fr e ≤ ((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ)) →
    ∀ fc : Fin 3 × Fin n → ℤ,
    (∀ e, -((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ) ≤ fc e ∧
      fc e ≤ ((((n / 450) * poolMaximum n) / 2 : ℕ) : ℤ)) →
    ∃ b : Cell n ≃ Fin (n*n),
      (∀ r, (rowSum b r : ℤ) - (rowSum oldReference r : ℤ) =
        2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun x => x.2) (fun x => p x.1 x.2) fr e r) ∧
      (∀ c, (columnSum b c : ℤ) - (columnSum oldReference c : ℤ) =
        2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun x => x.2) (fun x => p x.1 x.2) fc e c) ∧
      mainSum b = mainSum oldReference ∧ antiSum b = antiSum oldReference ∧
      (∀ c ∈ packedRectangleSupport hs choice, entry b c = entry oldReference c) ∧
      (∀ c ∉ roles, entry b c = entry ordered c) ∧
      roles.image (entry b) = roles.image (entry ordered) ∧
      Set.range (entry b) = pool n ∧ Function.Injective (entry b)

end
end Sude
