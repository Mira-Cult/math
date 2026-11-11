import Sude.FWGrowthOrdinaryRectangleMass
import Sude.FWGrowthRectangleMembership

/-! Actual FW growth endpoint membership and the resulting twelve ordinary
row/column incidences. This establishes no allocation or line bound. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

/-- A growth endpoint lies in the actual FW active rectangle support exactly
when its pair index is not an ordinary layer index. -/
theorem fw_growth_active_rectangle_endpoint_iff {n P : ℕ} (hP : P ≤ 238)
    (hoff : 5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)+P*(4*6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (preRows preCols gr gc : List (LayerPacking.Layer n))
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) (preRows ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (preRows ++ gr))) (preCols ++ gc)) :
    let offset := 5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice gr gc hgr hgc
    let active := activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)
    ∀ j i side, cells ((j,i),side) ∈ active ↔ i ∉ fwGrowthOrdinarySlots n := by
  classical
  dsimp only
  have hsupp := fw_growth_rectangle_ordinary_support hP hoff hs choice preRows preCols gr gc hgr hgc hrows hcols
  dsimp only at hsupp
  let hfit : (4*6)*2+2*(3*n) ≤ 6*(n+8) := by omega
  let hdiag : (4*6)*2 ≤ 6*(n+8) := by omega
  let hexact : (4*6)*2+2*(3*n) = 6*(n+8) := by omega
  let e := Equiv.ofBijective (prefixStagePairSlot (d := 6) (layers := 3) (n := n) hfit hdiag)
    (prefixStagePairSlot_bijective hfit hdiag hexact)
  intro j i side
  obtain ⟨t, ht⟩ := e.surjective i
  subst i
  cases t with
  | inl p =>
    rcases p with ⟨rect,pair⟩
    have hm := hsupp.1 j rect pair side
    have hn : prefixDiagonalPairIndex hdiag (rect,pair) ∉ fwGrowthOrdinarySlots n := by
      intro h
      obtain ⟨t, _, ht⟩ := Finset.mem_image.mp h
      exact (prefixOrdinary_ne_diagonal hfit hdiag t (rect,pair)) ht
    simpa only [e, Equiv.ofBijective_apply, prefixStagePairSlot] using Iff.intro (fun _ => hn) (fun _ => hm)
  | inr p =>
    rcases p with ⟨network,k,edge⟩
    have hi : prefixOrdinaryPairIndex hfit (network,k,edge) ∈ fwGrowthOrdinarySlots n :=
      Finset.mem_image.mpr ⟨(network,k,edge), Finset.mem_univ _, rfl⟩
    have hm : btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc
          ((j, prefixOrdinaryPairIndex hfit (network,k,edge)),side) ∉
        activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP) := by
      fin_cases network
      · exact hsupp.2.1 j k edge side
      · exact hsupp.2.2 j k edge side
    simpa only [e, Equiv.ofBijective_apply, prefixStagePairSlot] using Iff.intro (fun h => False.elim (hm h)) (fun h => False.elim (h hi))

/-- The exact physical active-rectangle restriction removes every growth
rectangle endpoint and leaves twelve ordinary incidences per stage and line. -/
theorem fw_growth_active_rectangle_ordinary_line_mass {n P : ℕ} (hP : P ≤ 238)
    (hoff : 5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)+P*(4*6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (preRows preCols gr gc : List (LayerPacking.Layer n))
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) (preRows ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (preRows ++ gr))) (preCols ++ gc)) :
    let offset := 5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice gr gc hgr hgc
    let active := activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)
    (∀ j : Fin P, ∀ r : Fin n,
      (∑ i : Fin (6*(n+8)), (physicalPairLineWeight cells (fun z => z.1 = r) (j,i) -
        physicalPairLineWeight cells (fun z => z.1 = r ∧ z ∈ active) (j,i))) = 12) ∧
    (∀ j : Fin P, ∀ c : Fin n,
      (∑ i : Fin (6*(n+8)), (physicalPairLineWeight cells (fun z => z.2 = c) (j,i) -
        physicalPairLineWeight cells (fun z => z.2 = c ∧ z ∈ active) (j,i))) = 12) := by
  exact fw_growth_ordinary_rectangle_line_mass _ hoff hs choice gr gc hgr hgc _
    (fw_growth_active_rectangle_endpoint_iff hP hoff hs choice preRows preCols gr gc hgr hgc hrows hcols)

end
end Sude
