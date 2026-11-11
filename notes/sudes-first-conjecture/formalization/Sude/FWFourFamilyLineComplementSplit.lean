import Sude.FWFourFamilyRoleCoverage
import Sude.FWGroupedBridgeWideGeometry
import Sude.FWRoleSupportForNetworks

/-! Exact bookkeeping for the single physical complement of bridge and wide.
The reserved spare and genuinely free cells remain separate. This identity
contains no estimate and charges no spare-cell deviation. -/
namespace Sude
noncomputable section

/-- A line outside the bridge and wide roles consists exactly of seed, growth,
reserved spare, and free cells. The roles and reservation are on the same
physical square; `value` may be its entry function or any other function. -/
theorem four_family_line_complement_split {α : Type*} [DecidableEq α]
    (line bridge seed wide growth full : Finset α) (value : α → ℝ)
    (hbs : Disjoint (bridge ∪ wide) seed)
    (hbg : Disjoint (bridge ∪ wide) growth)
    (hsg : Disjoint seed growth)
    (hfull : ((bridge ∪ seed) ∪ wide) ∪ growth ⊆ full) :
    let roles := ((bridge ∪ seed) ∪ wide) ∪ growth
    (∑ z ∈ line \ (bridge ∪ wide), value z) =
      (∑ z ∈ line ∩ seed, value z) + (∑ z ∈ line ∩ growth, value z) +
      (∑ z ∈ line ∩ (full \ roles), value z) + (∑ z ∈ line \ full, value z) := by
  classical
  dsimp only
  let roles := ((bridge ∪ seed) ∪ wide) ∪ growth
  let S := line ∩ seed
  let G := line ∩ growth
  let R := line ∩ (full \ roles)
  let F := line \ full
  have hbs' := Finset.disjoint_left.mp hbs
  have hbg' := Finset.disjoint_left.mp hbg
  have hsg' := Finset.disjoint_left.mp hsg
  have hpart : line \ (bridge ∪ wide) = ((S ∪ G) ∪ R) ∪ F := by
    ext x
    simp only [S, G, R, F, roles, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_union]
    constructor
    · intro hx
      have hf : x ∈ ((bridge ∪ seed) ∪ wide) ∪ growth → x ∈ full := fun hx => hfull hx
      simp only [Finset.mem_union] at hf
      by_cases hf' : x ∈ full <;> simp_all <;> tauto
    · intro hx
      have hbsx : (x ∈ bridge ∨ x ∈ wide) → x ∈ seed → False := by
        intro h1 h2
        exact hbs' (Finset.mem_union.mpr h1) h2
      have hbgx : (x ∈ bridge ∨ x ∈ wide) → x ∈ growth → False := by
        intro h1 h2
        exact hbg' (Finset.mem_union.mpr h1) h2
      have hf : x ∈ ((bridge ∪ seed) ∪ wide) ∪ growth → x ∈ full := fun hx => hfull hx
      simp only [Finset.mem_union] at hf
      tauto
  have hSG : Disjoint S G := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact hsg' (Finset.mem_inter.mp hx).2 (Finset.mem_inter.mp hy).2
  have hSGR : Disjoint (S ∪ G) R := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [S, G, R, roles, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at hx hy
    tauto
  have hSGRF : Disjoint ((S ∪ G) ∪ R) F := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [S, G, R, F, roles, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at hx hy
    have hf : x ∈ ((bridge ∪ seed) ∪ wide) ∪ growth → x ∈ full := fun hx => hfull hx
    simp only [Finset.mem_union] at hf
    tauto
  rw [hpart, Finset.sum_union hSGRF, Finset.sum_union hSGR, Finset.sum_union hSG]


set_option maxRecDepth 32768
set_option maxHeartbeats 800000

/-- The same split for the actual four FW role families. The reservation may
be enlarged, including after diagonal completion; consequently its spare term
uses this supplied reservation, not the earlier geometric spare. -/
theorem fw_physical_four_family_line_complement_split {n P : ℕ}
    (hP : P ≤ 238)
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
    (full : Finset (Cell n))
    (hgeofull : packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc)) ⊆ full)
    (line : Finset (Cell n)) (value : Cell n → ℝ) :
    let bridge := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
    let wide := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
    let seed := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    let growth := btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc
    let B := Finset.univ.image bridge
    let W := Finset.univ.image wide
    let S := Finset.univ.image seed
    let G := Finset.univ.image growth
    let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)
    (∑ z ∈ line \ (B ∪ W), value z) =
      (∑ z ∈ line ∩ S, value z) + (∑ z ∈ line ∩ G, value z) +
      (∑ z ∈ line ∩ (full \ roles), value z) + (∑ z ∈ line \ full, value z) := by
  classical
  dsimp only
  let bridge := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
  let wide := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
  let seed := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
  let growth := btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc
  let B := Finset.univ.image bridge
  let W := Finset.univ.image wide
  let S := Finset.univ.image seed
  let G := Finset.univ.image growth
  let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)
  obtain ⟨hfamily, _⟩ := fw_four_family_pair_cells_injective hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
  let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc
  change Function.Injective cells at hfamily
  have hbs : ∀ x y, bridge x ≠ seed y := by
    intro x y h
    have he := hfamily (show cells (Sum.inl (Sum.inl (Sum.inl (fwBlockPairIndex 5 n x)))) =
      cells (Sum.inl (Sum.inl (Sum.inr y))) from h)
    simp only [Sum.inl.injEq, reduceCtorEq] at he
  have hbg : ∀ x y, bridge x ≠ growth y := by
    intro x y h
    have he := hfamily (show cells (Sum.inl (Sum.inl (Sum.inl (fwBlockPairIndex 5 n x)))) =
      cells (Sum.inr y) from h)
    simp only [reduceCtorEq] at he
  have hws : ∀ x y, wide x ≠ seed y := by
    intro x y h
    have he := hfamily (show cells (Sum.inl (Sum.inr (fwBlockPairIndex (3 * (n / 450)) n x))) =
      cells (Sum.inl (Sum.inl (Sum.inr y))) from h)
    simp only [Sum.inl.injEq, reduceCtorEq] at he
  have hwg : ∀ x y, wide x ≠ growth y := by
    intro x y h
    have he := hfamily (show cells (Sum.inl (Sum.inr (fwBlockPairIndex (3 * (n / 450)) n x))) =
      cells (Sum.inr y) from h)
    simp only [reduceCtorEq] at he
  have hsg : ∀ x y, seed x ≠ growth y := by
    intro x y h
    have he := hfamily (show cells (Sum.inl (Sum.inl (Sum.inr x))) = cells (Sum.inr y) from h)
    simp only [reduceCtorEq] at he
  have hBS : Disjoint (B ∪ W) S := by
    apply Finset.disjoint_left.mpr
    intro z hz hs'
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hs'
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hz
      exact hbs x y (hx.trans hy.symm)
    · obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hz
      exact hws x y (hx.trans hy.symm)
  have hBG : Disjoint (B ∪ W) G := by
    apply Finset.disjoint_left.mpr
    intro z hz hg'
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hg'
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hz
      exact hbg x y (hx.trans hy.symm)
    · obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hz
      exact hwg x y (hx.trans hy.symm)
  have hSG : Disjoint S G := by
    apply Finset.disjoint_left.mpr
    intro z hz hg'
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hz
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hg'
    exact hsg x y (hx.trans hy.symm)
  have hbimage : B = Finset.univ.image (fwBridgePhysicalPairCells hrect hs choice br bc hbr hbc) := by
    change Finset.univ.image (_ ∘ fwBlockPairIndex 5 n) = _
    rw [← Finset.image_image, Finset.image_univ_of_surjective (fwBlockPairIndex 5 n).surjective]
  have hwimage : W = Finset.univ.image (fwWidePhysicalPairCells hwide hs choice wr wc hwr hwc) := by
    change Finset.univ.image (_ ∘ fwBlockPairIndex (3 * (n / 450)) n) = _
    rw [← Finset.image_image, Finset.image_univ_of_surjective (fwBlockPairIndex (3 * (n / 450)) n).surjective]
  have hcover : ((B ∪ S) ∪ W) ∪ G = roles := by
    rw [hbimage, hwimage]
    exact fw_four_family_pair_cells_cover_roles hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc
  have hfull : roles ⊆ full :=
    (fw_role_support_for_trace_networks hP hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols).2.2.1.trans hgeofull
  have h := four_family_line_complement_split line B S W G full value hBS hBG hSG
    (hcover ▸ hfull)
  dsimp only at h
  rw [hcover] at h
  exact h

end
end Sude
