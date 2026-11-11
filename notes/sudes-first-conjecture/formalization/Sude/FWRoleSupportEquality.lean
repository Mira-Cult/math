import Sude.FWJointPackedOccupancy
import Sude.FWGrowthEarlyGeometry
import Sude.BTGrowingOffsetPhysical

/-! Geometric coverage of FW role-cell maps. No claim about values or preservation. -/
namespace Sude
noncomputable section

private theorem active_support_union {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (a b : Finset (Fin L)) :
    activeRectangleSupport hs choice (a ∪ b) =
      activeRectangleSupport hs choice a ∪ activeRectangleSupport hs choice b := by
  classical
  ext z
  simp only [activeRectangleSupport, Finset.mem_image, Finset.mem_product,
    Finset.mem_univ, and_true, Finset.mem_union]
  aesop

private theorem active_support_image {L n M : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (f : Fin M → Fin L) :
    activeRectangleSupport hs choice (Finset.univ.image f) =
      Finset.univ.image (fun x : Fin M × Fin 4 => packedRectangleCorner hs choice (f x.1, x.2)) := by
  classical
  ext z
  simp only [activeRectangleSupport, Finset.mem_image, Finset.mem_product, Finset.mem_univ,
    and_true, true_and]
  constructor
  · rintro ⟨⟨i, j⟩, ⟨k, rfl⟩, h⟩
    exact ⟨(k, j), h⟩
  · rintro ⟨⟨i, j⟩, h⟩
    exact ⟨(f i, j), ⟨i, rfl⟩, h⟩

private theorem layer_support_append {n : ℕ} (a b : List (LayerPacking.Layer n)) :
    LayerPacking.layersSupport (a ++ b) = LayerPacking.layersSupport a ∪ LayerPacking.layersSupport b := by
  induction a with
  | nil => simp [LayerPacking.layersSupport]
  | cons x xs ih => simp [LayerPacking.layersSupport, ih, Finset.union_assoc]

private theorem growing_role_coverage {P d r n L : ℕ} (offset : ℕ)
    (hoff : offset + P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = P * r) (hc : cols.length = P * r) :
    Finset.univ.image (btGrowingOffsetCells offset hoff hs choice rows cols hr hc) =
      activeRectangleSupport hs choice
        (Finset.univ.image (btGrowingOffsetRectangle (P := P) (d := d) offset hoff)) ∪
      LayerPacking.layersSupport rows ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport cols) := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
    rcases x with ⟨i, s⟩ | (⟨i, x⟩ | ⟨i, x⟩)
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨(btGrowingOffsetRectangle offset hoff i, s),
        Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, Finset.mem_univ _⟩, rfl⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact LayerPacking.layerSupport_subset _ rows (List.get_mem rows _)
        (LayerPacking.sequenceCell_mem rows _ _)
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨_, LayerPacking.layerSupport_subset _ cols (List.get_mem cols _)
        (LayerPacking.sequenceCell_mem cols _ _), rfl⟩
  · intro hz
    rcases Finset.mem_union.mp hz with hz | hz
    · rcases Finset.mem_union.mp hz with hz | hz
      · obtain ⟨⟨j, s⟩, hj, rfl⟩ := Finset.mem_image.mp hz
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_product.mp hj).1
        dsimp only at hi
        subst j
        exact Finset.mem_image.mpr ⟨Sum.inl (i, s), Finset.mem_univ _, rfl⟩
      · obtain ⟨⟨i, x⟩, hx⟩ := LayerPacking.sequenceCell_covers rows z hz
        refine Finset.mem_image.mpr ⟨Sum.inr (Sum.inl (Fin.cast hr i, x)), Finset.mem_univ _, ?_⟩
        simpa [btGrowingOffsetCells] using hx
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨⟨i, x⟩, hx⟩ := LayerPacking.sequenceCell_covers cols y hy
      refine Finset.mem_image.mpr ⟨Sum.inr (Sum.inr (Fin.cast hc i, x)), Finset.mem_univ _, ?_⟩
      simpa [btGrowingOffsetCells] using congrArg Prod.swap hx

private theorem fw_family_corners {n P : ℕ} (hP : P ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool) :
    activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP) =
    ((Finset.univ.image (fun x : Fin (5 * (4 * 6)) × Fin 4 =>
      packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect x.1, x.2)) ∪
      Finset.univ.image (fun x : Fin (16 * (4 * 6)) × Fin 4 =>
      packedRectangleCorner hs choice (fwSeedRectangle hseed x.1, x.2))) ∪
      Finset.univ.image (fun x : Fin ((3 * (n / 450)) * (4 * 6)) × Fin 4 =>
      packedRectangleCorner hs choice (fwWideRectangle hwide x.1, x.2))) ∪
      Finset.univ.image (fun x : Fin (P * (4 * 6)) × Fin 4 =>
      packedRectangleCorner hs choice (btGrowingOffsetRectangle
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff x.1, x.2)) := by
  classical
  rw [fw_active_labels_eq_family_union, active_support_union, active_support_union, active_support_union]
  simp only [active_support_image]


private theorem seq_image {n : ℕ} (layers : List (LayerPacking.Layer n)) :
    Finset.univ.image (LayerPacking.sequenceCell layers) = LayerPacking.layersSupport layers := by
  ext z
  constructor
  · intro hz
    obtain ⟨⟨i, e⟩, _, rfl⟩ := Finset.mem_image.mp hz
    exact LayerPacking.layerSupport_subset _ layers (List.get_mem layers i)
      (LayerPacking.sequenceCell_mem layers i e)
  · intro hz
    obtain ⟨x, hx⟩ := LayerPacking.sequenceCell_covers layers z hz
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hx⟩

private def index {J n m : ℕ} (hlen : m = J * 3)
    (x : (Fin J × (Fin 3 × Fin n)) × Bool) : Fin m × (Fin n × Bool) :=
  (Fin.cast hlen.symm (finProdFinEquiv (x.1.1, x.1.2.1)), (x.1.2.2, x.2))

private theorem index_surj {J n m : ℕ} (hlen : m = J * 3) :
    Function.Surjective (index (n := n) hlen) := by
  rintro ⟨i, e, b⟩
  let jk : Fin J × Fin 3 := finProdFinEquiv.symm (Fin.cast hlen i)
  refine ⟨((jk.1, jk.2, e), b), ?_⟩
  apply Prod.ext
  · change Fin.cast hlen.symm (finProdFinEquiv jk) = i
    rw [show finProdFinEquiv jk = Fin.cast hlen i from Equiv.apply_symm_apply finProdFinEquiv _]
    simp
  · rfl

private def ordinary {J n : ℕ} (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = J * 3) (hc : cols.length = J * 3)
    (x : (Fin J × (Fin 3 × Fin n)) × (Bool × Bool)) : Cell n :=
  if x.2.1 then (LayerPacking.sequenceCell cols (index hc (x.1, x.2.2))).swap
  else LayerPacking.sequenceCell rows (index hr (x.1, x.2.2))

private theorem ordinary_image {J n : ℕ} (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = J * 3) (hc : cols.length = J * 3) :
    Finset.univ.image (ordinary rows cols hr hc) =
      LayerPacking.layersSupport rows ∪ LayerPacking.transposeCells (LayerPacking.layersSupport cols) := by
  ext z
  constructor
  · intro hz
    obtain ⟨⟨a, net, side⟩, _, rfl⟩ := Finset.mem_image.mp hz
    cases net
    · apply Finset.mem_union_left
      simp only [ordinary, Bool.false_eq_true, ↓reduceIte]
      rw [← seq_image]
      exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
    · apply Finset.mem_union_right
      simp only [ordinary, ↓reduceIte]
      apply Finset.mem_image.mpr
      refine ⟨_, ?_, rfl⟩
      rw [← seq_image]
      exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  · intro hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨q, hq⟩ := LayerPacking.sequenceCell_covers rows z hz
      obtain ⟨⟨a, b⟩, hi⟩ := index_surj hr q
      exact Finset.mem_image.mpr ⟨(a, false, b), Finset.mem_univ _, by simpa [ordinary, hi] using hq⟩
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨q, hq⟩ := LayerPacking.sequenceCell_covers cols y hy
      obtain ⟨⟨a, b⟩, hi⟩ := index_surj hc q
      exact Finset.mem_image.mpr ⟨(a, true, b), Finset.mem_univ _, by simp [ordinary, hi, hq]⟩

private theorem bridge_image {n : ℕ} (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3) :
    Finset.univ.image (fwBridgeLayerCells rows cols hr hc) =
      LayerPacking.layersSupport rows ∪ LayerPacking.transposeCells (LayerPacking.layersSupport cols) := by
  exact ordinary_image rows cols hr hc

private theorem wide_image {n : ℕ} (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3) :
    Finset.univ.image (fwWideOrdinaryCells rows cols hr hc) =
      LayerPacking.layersSupport rows ∪ LayerPacking.transposeCells (LayerPacking.layersSupport cols) := by
  exact ordinary_image rows cols hr hc

private theorem seed_image {n : ℕ} (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = 16 * 3) (hc : cols.length = 16 * 3) :
    Finset.univ.image (fwSeedOrdinaryCells rows cols hr hc) =
      LayerPacking.layersSupport rows ∪ LayerPacking.transposeCells (LayerPacking.layersSupport cols) := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
    cases x with
    | inl x =>
      apply Finset.mem_union_left
      rw [← seq_image]
      exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
    | inr x =>
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨_, ?_, rfl⟩
      rw [← seq_image]
      exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  · intro hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨⟨i, e, b⟩, hq⟩ := LayerPacking.sequenceCell_covers rows z hz
      refine Finset.mem_image.mpr ⟨Sum.inl (Fin.cast hr i, (e, b)), Finset.mem_univ _, ?_⟩
      simpa [fwSeedOrdinaryCells] using hq
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨⟨i, e, b⟩, hq⟩ := LayerPacking.sequenceCell_covers cols y hy
      refine Finset.mem_image.mpr ⟨Sum.inr (Fin.cast hc i, (e, b)), Finset.mem_univ _, ?_⟩
      simp [fwSeedOrdinaryCells, hq]


private theorem combined_layers {n : ℕ} (br sr wr gr bc sc wc gc : List (LayerPacking.Layer n)) :
    LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc)) =
    (((LayerPacking.layersSupport br ∪ LayerPacking.transposeCells (LayerPacking.layersSupport bc)) ∪
      (LayerPacking.layersSupport sr ∪ LayerPacking.transposeCells (LayerPacking.layersSupport sc))) ∪
      (LayerPacking.layersSupport wr ∪ LayerPacking.transposeCells (LayerPacking.layersSupport wc))) ∪
      (LayerPacking.layersSupport gr ∪ LayerPacking.transposeCells (LayerPacking.layersSupport gc)) := by
  simp only [layer_support_append, LayerPacking.transposeCells, Finset.image_union]
  ac_rfl



private theorem rectangle_image {L n A : ℕ} (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (f : Fin A → Fin L) :
    Finset.univ.image (fun x : Fin A × Fin 4 => packedRectangleCorner hs choice (f x.1, x.2)) =
    activeRectangleSupport hs choice (Finset.univ.image f) := by
  ext z
  simp only [activeRectangleSupport, Finset.mem_image, Finset.mem_univ, Finset.mem_product, true_and, and_true]
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    exact ⟨(f a, b), ⟨a, rfl⟩, rfl⟩
  · rintro ⟨⟨i, b⟩, ⟨a, rfl⟩, rfl⟩
    exact ⟨(a, b), rfl⟩


private theorem wide_physical_image {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3) :
    Finset.univ.image (fwWidePhysicalCells hwide hs choice rows cols hr hc) =
      activeRectangleSupport hs choice (Finset.univ.image (fwWideRectangle hwide)) ∪
      LayerPacking.layersSupport rows ∪ LayerPacking.transposeCells (LayerPacking.layersSupport cols) := by
  have hsum : Finset.univ.image (fwWidePhysicalCells hwide hs choice rows cols hr hc) =
      Finset.univ.image (fun x : Fin ((3 * (n / 450)) * (4 * 6)) × Fin 4 =>
        packedRectangleCorner hs choice (fwWideRectangle hwide x.1, x.2)) ∪
      Finset.univ.image (fwWideOrdinaryCells rows cols hr hc) := by
    ext z
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨x, rfl⟩
      cases x with
      | inl x => exact Or.inl ⟨x, rfl⟩
      | inr x => exact Or.inr ⟨x, rfl⟩
    · rintro (⟨x, rfl⟩ | ⟨x, rfl⟩)
      · exact ⟨Sum.inl x, rfl⟩
      · exact ⟨Sum.inr x, rfl⟩
  rw [hsum, rectangle_image, wide_image]
  ext z
  simp only [Finset.mem_union]
  tauto



/-- The geometric union of all actual early role cells and the offset-growth
role image equals exactly the active-label rectangles and supplied ordinary
layer supports. No value or preservation property is asserted. -/
theorem fw_role_cells_eq_active_support {n P : ℕ} (hP : P ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3) :
    fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6))
        hoff hs choice gr gc hgr hgc) =
    fwActiveRectangleLayerSupport hP hs choice (((br ++ sr) ++ wr) ++ gr) (((bc ++ sc) ++ wc) ++ gc) := by
  classical
  rw [fwGrowthEarlyRoleCells, wide_physical_image, bridge_image, seed_image,
    growing_role_coverage]
  simp only [active_support_image]
  rw [fwActiveRectangleLayerSupport, fw_family_corners hP hrect hseed hwide hoff hs choice]
  simp only [layer_support_append, LayerPacking.transposeCells, Finset.image_union]
  ac_rfl

end
end Sude
