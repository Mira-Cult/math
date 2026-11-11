import Sude.FWFourFamilyStageTotals
import Sude.FWRoleSupportForNetworks

/-! Recover the original stage owner of actual packed rectangle cells by
inverting the injective four-family physical cell map. No value or score
assumption is used here. -/
namespace Sude
noncomputable section

/-- A total owner function; its values off the physical image are immaterial. -/
def physicalPairStageOwner {I J α : Type*} [Nonempty I] [Nonempty J]
    (cells : (I × J) × Bool → α) (z : α) : I :=
  (Function.invFun cells z).1.1

/-- Reindex a rectangle line sum by the actual physical stage/slot/end labels.
The rectangle set must be contained in the image of the injective pair map. -/
theorem physical_pair_stage_owner_reindex {I J α : Type*}
    [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] [DecidableEq α]
    (cells : (I × J) × Bool → α) (hinj : Function.Injective cells)
    (rect line : Finset α) (hcover : rect ⊆ Finset.univ.image cells)
    (f : I → ℝ) :
    (∀ j i side, physicalPairStageOwner cells (cells ((j,i),side)) = j) ∧
    (∑ z ∈ rect ∩ line, f (physicalPairStageOwner cells z)) =
      ∑ t ∈ (Finset.univ : Finset ((I × J) × Bool)).filter (fun t => cells t ∈ rect ∩ line),
        f t.1.1 := by
  classical
  have howner (t : (I × J) × Bool) : physicalPairStageOwner cells (cells t) = t.1.1 := by
    unfold physicalPairStageOwner
    rw [Function.leftInverse_invFun hinj t]
  refine ⟨fun j i side => howner ((j,i),side), ?_⟩
  have hset : rect ∩ line = ((Finset.univ : Finset ((I × J) × Bool)).filter
      (fun t => cells t ∈ rect ∩ line)).image cells := by
    ext z
    constructor
    · intro hz
      have hz' := hcover (Finset.mem_inter.mp hz).1
      obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hz'
      exact Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht ▸ hz⟩, ht⟩
    · intro hz
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp ht).2
  conv_lhs => rw [hset, Finset.sum_image (fun x _ y _ h => hinj h)]
  apply Finset.sum_congr rfl
  intro t ht
  rw [howner]

/-- The physical endpoint reindex is exactly the usual pair-line weight
restricted to rectangle cells, for arbitrary original-stage values. -/
theorem physical_pair_stage_owner_weighted {n : ℕ} {I J : Type*}
    [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
    (cells : (I × J) × Bool → Cell n) (hinj : Function.Injective cells)
    (rect line : Finset (Cell n)) (hcover : rect ⊆ Finset.univ.image cells)
    (f : I → ℝ) :
    (∑ z ∈ rect ∩ line, f (physicalPairStageOwner cells z)) =
      ∑ j : I, ∑ i : J, physicalPairLineWeight cells (fun z => z ∈ rect ∩ line) (j,i) * f j := by
  classical
  rw [(physical_pair_stage_owner_reindex cells hinj rect line hcover f).2]
  rw [Finset.sum_filter]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  unfold physicalPairLineWeight
  split_ifs <;> ring

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

/-- Actual FW rectangle line means reindex by the original four-family stage
labels. All stages, slots, and endpoint sides use one physical cell map. -/
theorem fw_rectangle_stage_owner_reindex {n P : ℕ} (hP : P ≤ 238)
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
    (line : Finset (Cell n)) (f : FWFourStageIndex n P → ℝ) :
    letI : Nonempty (FWFourStageIndex n P) := ⟨Sum.inl (Sum.inl (Sum.inl ⟨0, by omega⟩))⟩
    letI : Nonempty (Fin (6 * (n + 8))) := ⟨⟨0, by omega⟩⟩
    let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n P
    let rect := activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)
    (∀ j i side, physicalPairStageOwner cells (cells ((j,i),side)) = j) ∧
    ((∑ z ∈ rect ∩ line, f (physicalPairStageOwner cells z)) =
      ∑ t ∈ (Finset.univ : Finset ((FWFourStageIndex n P × Fin (6 * (n + 8))) × Bool)).filter
        (fun t => cells t ∈ rect ∩ line), f t.1.1) ∧
    ((∑ z ∈ rect ∩ line, f (physicalPairStageOwner cells z)) =
      ∑ j : FWFourStageIndex n P, ∑ i : Fin (6 * (n + 8)),
        physicalPairLineWeight cells (fun z => z ∈ rect ∩ line) (j,i) * f j) := by
  classical
  dsimp only
  let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n P
  let rect := activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)
  have hp := fw_four_family_pair_cells_injective hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
  dsimp only at hp
  have hi : Function.Injective cells := hp.1.comp (fwFourStageInputEquiv n P).injective
  have him : Finset.univ.image cells =
      fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
        Finset.univ.image (btGrowingOffsetCells
          (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc) := by
    simpa only [cells, ← Finset.image_image, Finset.image_univ_of_surjective
      (fwFourStageInputEquiv n P).surjective] using hp.2
  have hrole := fw_role_cells_eq_active_support hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc
  have hcover : rect ⊆ Finset.univ.image cells := by
    rw [him, hrole]
    intro z hz
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hz)
  have h := physical_pair_stage_owner_reindex cells hi rect line hcover f
  exact ⟨h.1, h.2, physical_pair_stage_owner_weighted cells hi rect line hcover f⟩

end
end Sude
