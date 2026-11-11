import Sude.FWWideRectangleOffset
import Sude.FWWideLayerPacking

/-! Exact FW wide role allocation and physical cell geometry. No wide
prime values or later controller layout are selected or installed here. -/
namespace Sude
noncomputable section

/-- Wide diagonal and ordinary roles for the source's `3K` stages. -/
abbrev FWWideInputs (n : ℕ) :=
  (Fin ((3 * (n / 450)) * (4 * 6)) × Fin 4) ⊕
    ((Fin (3 * (n / 450)) × (Fin 3 × Fin n)) × (Bool × Bool))

/-- The 24 diagonal blocks and the 3n ordinary blocks exactly partition each
stage's `3(n+8)` double blocks. -/
def fwWideControllerSlot (n : ℕ) : FWWideInputs n →
    (Fin (3 * (n / 450)) × Fin (3 * (n + 8))) × Fin 4 :=
  Sum.elim
    (fun x => (bridgeDiagonalBlockSelect (J := 3 * (n / 450)) (d := 6) (by omega) x.1, x.2))
    (bridgeOrdinarySlot (J := 3 * (n / 450)) (r := 3) (d := 6) (by omega))

/-- The source split is bijective; the two ordinary networks use the two
different pairs in each ordinary block. -/
theorem fwWideControllerSlot_bijective (n : ℕ) :
    Function.Bijective (fwWideControllerSlot n) := by
  have hinj : Function.Injective (fwWideControllerSlot n) := by
    intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        have hb := congrArg Prod.fst h
        have hs := congrArg Prod.snd h
        have hxy : x.1 = y.1 := bridgeDiagonalBlockSelect_injective
          (J := 3 * (n / 450)) (d := 6) (by omega) hb
        exact congrArg Sum.inl (Prod.ext hxy hs)
      | inr y =>
        exfalso
        exact bridgeOrdinarySlot_ne_diagonal (J := 3 * (n / 450)) (r := 3) (d := 6)
          (by omega) (by omega) y x.1 x.2 h.symm
    | inr x =>
      cases y with
      | inl y =>
        exfalso
        exact bridgeOrdinarySlot_ne_diagonal (J := 3 * (n / 450)) (r := 3) (d := 6)
          (by omega) (by omega) x y.1 y.2 h
      | inr y =>
        exact congrArg Sum.inr (bridgeOrdinarySlot_injective
          (J := 3 * (n / 450)) (r := 3) (d := 6) (by omega) h)
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨hinj, ?_⟩
  simp only [FWWideInputs, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring

/-- Flatten the stage/block labels to the index used by the actual wide
block-sequence selection theorem. -/
def fwWideFlatSlot (n : ℕ) (x : FWWideInputs n) :
    Fin ((3 * (n / 450)) * (3 * (n + 8))) × Fin 4 :=
  (finProdFinEquiv (fwWideControllerSlot n x).1, (fwWideControllerSlot n x).2)

theorem fwWideFlatSlot_bijective (n : ℕ) : Function.Bijective (fwWideFlatSlot n) := by
  constructor
  · intro x y h
    apply (fwWideControllerSlot_bijective n).1
    exact Prod.ext (finProdFinEquiv.injective (congrArg Prod.fst h)) (congrArg (fun z : Fin ((3 * (n / 450)) * (3 * (n + 8))) × Fin 4 => z.2) h)
  · rintro ⟨i, side⟩
    obtain ⟨x, hx⟩ := (fwWideControllerSlot_bijective n).2 (finProdFinEquiv.symm i, side)
    refine ⟨x, ?_⟩
    unfold fwWideFlatSlot
    rw [hx]
    exact Prod.ext (Equiv.apply_symm_apply finProdFinEquiv i) rfl

/-- Stage, within-stage layer, edge and side as an actual list index. -/
def fwWideLayerIndex {n m : ℕ} (hlen : m = (3 * (n / 450)) * 3)
    (x : (Fin (3 * (n / 450)) × (Fin 3 × Fin n)) × Bool) : Fin m × (Fin n × Bool) :=
  (Fin.cast hlen.symm (finProdFinEquiv (x.1.1, x.1.2.1)), (x.1.2.2, x.2))

theorem fwWideLayerIndex_injective {n m : ℕ} (hlen : m = (3 * (n / 450)) * 3) :
    Function.Injective (fwWideLayerIndex (n := n) hlen) := by
  rintro ⟨⟨j, k, e⟩, s⟩ ⟨⟨j', k', e'⟩, s'⟩ h
  have hi := congrArg Prod.fst h
  have he := congrArg (fun z : Fin m × (Fin n × Bool) => z.2.1) h
  have hs := congrArg (fun z : Fin m × (Fin n × Bool) => z.2.2) h
  have hjk : (j, k) = (j', k') := by
    apply finProdFinEquiv.injective
    exact Fin.cast_injective hlen.symm hi
  cases hjk
  cases he
  cases hs
  rfl

/-- The physical ordinary role uses row layers or transposed column layers. -/
def fwWideOrdinaryCells {n : ℕ} (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (x : (Fin (3 * (n / 450)) × (Fin 3 × Fin n)) × (Bool × Bool)) : Cell n :=
  if x.2.1 then (LayerPacking.sequenceCell cols (fwWideLayerIndex hc (x.1, x.2.2))).swap
  else LayerPacking.sequenceCell rows (fwWideLayerIndex hr (x.1, x.2.2))

/-- Use wide offset rectangles and the supplied wide layers for all roles. -/
def fwWidePhysicalCells {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3) :
    FWWideInputs n → Cell n :=
  Sum.elim (fun x => packedRectangleCorner hs choice (fwWideRectangle hwide x.1, x.2))
    (fwWideOrdinaryCells rows cols hr hc)

/-- Provided the actual wide rectangles are free of the prior cells, the
packed wide role map is injective and avoids every supplied prior cell. The
layout base reserves all RP1 rectangles as well as the earlier layers. -/
theorem fwWidePhysicalCells_geometry {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (base prior : Finset (Cell n)) (hrectbase : packedRectangleSupport hs choice ⊆ base)
    (hprior : prior ⊆ base)
    (hdiagfree : ∀ x : Fin ((3 * (n / 450)) * (4 * 6)) × Fin 4,
      packedRectangleCorner hs choice (fwWideRectangle hwide x.1, x.2) ∉ prior)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (hrows : LayerPacking.PackedLayers base rows)
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (base ∪ LayerPacking.layersSupport rows)) cols)
    (hdisjoint : Disjoint (LayerPacking.layersSupport rows)
      (LayerPacking.transposeCells (LayerPacking.layersSupport cols))) :
    Function.Injective (fwWidePhysicalCells hwide hs choice rows cols hr hc) ∧
    (∀ x, fwWidePhysicalCells hwide hs choice rows cols hr hc x ∉ prior) := by
  have hrmem : ∀ x, LayerPacking.sequenceCell rows x ∈ LayerPacking.layersSupport rows := by
    intro x
    exact LayerPacking.layerSupport_subset (rows.get x.1) rows (List.get_mem rows x.1)
      (LayerPacking.sequenceCell_mem rows x.1 x.2)
  have hcmem : ∀ x, (LayerPacking.sequenceCell cols x).swap ∈
      LayerPacking.transposeCells (LayerPacking.layersSupport cols) := by
    intro x
    exact Finset.mem_image.mpr ⟨_, LayerPacking.layerSupport_subset (cols.get x.1) cols
      (List.get_mem cols x.1) (LayerPacking.sequenceCell_mem cols x.1 x.2), rfl⟩
  have hordInj : Function.Injective (fwWideOrdinaryCells rows cols hr hc) := by
    rintro ⟨a, ⟨network, side⟩⟩ ⟨b, ⟨network', side'⟩⟩ heq
    cases network <;> cases network'
    · simp only [fwWideOrdinaryCells, Bool.false_eq_true, ↓reduceIte] at heq
      have hidx := (fwWideLayerIndex_injective hr) (hrows.sequenceCell_injective heq)
      cases hidx
      rfl
    · simp only [fwWideOrdinaryCells, Bool.false_eq_true, ↓reduceIte] at heq
      exact False.elim (Finset.disjoint_left.mp hdisjoint (hrmem _) (heq ▸ hcmem _))
    · simp only [fwWideOrdinaryCells, Bool.false_eq_true, ↓reduceIte] at heq
      exact False.elim (Finset.disjoint_left.mp hdisjoint (heq ▸ hrmem _) (hcmem _))
    · simp only [fwWideOrdinaryCells, ↓reduceIte] at heq
      have heq' := congrArg Prod.swap heq
      simp only [Prod.swap_swap] at heq'
      have hidx := (fwWideLayerIndex_injective hc) (hcols.sequenceCell_injective heq')
      cases hidx
      rfl
  have hordFree : ∀ x, fwWideOrdinaryCells rows cols hr hc x ∉ base := by
    rintro ⟨a, ⟨network, side⟩⟩
    cases network
    · exact hrows.sequenceCell_unreserved _
    · intro hm
      exact (hcols.transposed_support_safe _ (hcmem _)).1 (Finset.mem_union_left _ hm)
  have hdiagInj : Function.Injective (fun x : Fin ((3 * (n / 450)) * (4 * 6)) × Fin 4 =>
      packedRectangleCorner hs choice (fwWideRectangle hwide x.1, x.2)) := by
    rintro ⟨i, s⟩ ⟨j, t⟩ h
    have heq := packedRectangleCorner_injective hs choice h
    exact Prod.ext (fwWideRectangle_injective hwide (congrArg Prod.fst heq)) (congrArg (fun z : Fin L × Fin 4 => z.2) heq)
  have hdiagInBase : ∀ x : Fin ((3 * (n / 450)) * (4 * 6)) × Fin 4,
      packedRectangleCorner hs choice (fwWideRectangle hwide x.1, x.2) ∈ base := by
    intro x
    apply hrectbase
    exact Finset.mem_image.mpr ⟨(fwWideRectangle hwide x.1, x.2), Finset.mem_univ _, rfl⟩
  constructor
  · intro x y heq
    rcases x with x | x <;> rcases y with y | y <;> dsimp only [fwWidePhysicalCells, Sum.elim_inl, Sum.elim_inr] at heq
    · exact congrArg Sum.inl (hdiagInj heq)
    · exact False.elim (hordFree y (heq ▸ hdiagInBase x))
    · exact False.elim (hordFree x (heq ▸ hdiagInBase y))
    · exact congrArg Sum.inr (hordInj heq)
  · intro x
    rcases x with x | x
    · exact hdiagfree x
    · intro hp
      exact hordFree x (hprior hp)

end
end Sude
