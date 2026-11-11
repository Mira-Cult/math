import Sude.LayerNetworks

/-! Simultaneous physical row-network switches on disjoint actual pairs.
Flow existence and selection of the needed subsets remain separate. -/
namespace Sude
noncomputable section

/-- Physical vertical pairs indexed by graph edges and stages. Every slot is
an actual cell of the prescribed pool placement, and distinct labels never
share a cell. -/
structure RowNetworkPairs {n : ℕ} (α : Type*) (a : Cell n ≃ Fin (n * n)) where
  low : α → Fin n
  high : α → Fin n
  column : α → Fin n
  rows_ne : ∀ k, low k ≠ high k
  gap : α → ℕ
  gap_at : ∀ k, entry a (high k, column k) = entry a (low k, column k) + gap k
  slots_injective : Function.Injective (fun x : α × Bool =>
    if x.2 then (high x.1, column x.1) else (low x.1, column x.1))
  low_main : ∀ k, (low k, column k) ∉ mainCells n
  high_main : ∀ k, (high k, column k) ∉ mainCells n
  low_anti : ∀ k, (low k, column k) ∉ antiCells n
  high_anti : ∀ k, (high k, column k) ∉ antiCells n

def rowNetworkSlot {n : ℕ} {α : Type*} {a : Cell n ≃ Fin (n * n)}
    (v : RowNetworkPairs α a) (x : α × Bool) : Cell n :=
  if x.2 then (v.high x.1, v.column x.1) else (v.low x.1, v.column x.1)

theorem rowNetworkSlot_injective {n : ℕ} {α : Type*} {a : Cell n ≃ Fin (n * n)}
    (v : RowNetworkPairs α a) : Function.Injective (rowNetworkSlot v) := v.slots_injective

def rowNetworkDelta {n : ℕ} {α : Type*} {a : Cell n ≃ Fin (n * n)}
    (v : RowNetworkPairs α a) (k : α) (r : Fin n) : ℤ :=
  (if v.low k = r then (v.gap k : ℤ) else 0) -
    (if v.high k = r then (v.gap k : ℤ) else 0)

/-- Exact effects and untouched-cell invariant for a set of physical swaps. -/
structure RowNetworkOutcome {n : ℕ} {α : Type*} [DecidableEq α]
    {a : Cell n ≃ Fin (n * n)} (v : RowNetworkPairs α a) (S : Finset α)
    (b : Cell n ≃ Fin (n * n)) : Prop where
  rows : ∀ r, (rowSum b r : ℤ) - (rowSum a r : ℤ) = ∑ k ∈ S, rowNetworkDelta v k r
  columns : ∀ c, columnSum b c = columnSum a c
  main : mainSum b = mainSum a
  anti : antiSum b = antiSum a
  outside_fixed : ∀ c, (∀ k ∈ S, c ≠ (v.low k, v.column k) ∧ c ≠ (v.high k, v.column k)) →
    entry b c = entry a c

/-- Swapping any finite subset of the supplied physical network pairs gives
exactly the sum of the corresponding signed row transfers. All other cells,
every column and both full diagonals are preserved. -/
theorem rowNetwork_toggle_subset {n : ℕ} {α : Type*} [DecidableEq α]
    (a : Cell n ≃ Fin (n * n)) (v : RowNetworkPairs α a) (S : Finset α) :
    ∃ b : Cell n ≃ Fin (n * n), RowNetworkOutcome v S b := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨a, ?_⟩
    constructor
    · intro r; simp
    · intro c; rfl
    · rfl
    · rfl
    · intro c hc; rfl
  | @insert k S hk ih =>
    obtain ⟨b, hb⟩ := ih
    have hslot_ne : ∀ l ∈ S, ∀ x y : Bool, rowNetworkSlot v (k, x) ≠ rowNetworkSlot v (l, y) := by
      intro l hl x y heq
      have hkl : k = l := congrArg Prod.fst (rowNetworkSlot_injective v heq)
      exact hk (hkl ▸ hl)
    have hlow : entry b (v.low k, v.column k) = entry a (v.low k, v.column k) := by
      apply hb.outside_fixed
      intro l hl
      exact ⟨by simpa [rowNetworkSlot] using hslot_ne l hl false false,
        by simpa [rowNetworkSlot] using hslot_ne l hl false true⟩
    have hhigh : entry b (v.high k, v.column k) = entry a (v.high k, v.column k) := by
      apply hb.outside_fixed
      intro l hl
      exact ⟨by simpa [rowNetworkSlot] using hslot_ne l hl true false,
        by simpa [rowNetworkSlot] using hslot_ne l hl true true⟩
    have hgap : entry b (v.high k, v.column k) = entry b (v.low k, v.column k) + v.gap k := by
      rw [hlow, hhigh]
      exact v.gap_at k
    let b' := swapPlacement b (v.low k, v.column k) (v.high k, v.column k)
    have hne : (v.low k, v.column k) ≠ (v.high k, v.column k) := by
      intro heq
      exact v.rows_ne k (congrArg Prod.fst heq)
    have hdiag := swapPlacement_diagonals_unchanged b _ _ hne
      (v.low_main k) (v.high_main k) (v.low_anti k) (v.high_anti k)
    refine ⟨b', ?_⟩
    constructor
    · intro r
      have hstep := verticalSwap_row_effect b (v.low k) (v.high k) (v.column k) r (v.rows_ne k)
      have hprev := hb.rows r
      have hgapZ : (entry b (v.high k, v.column k) : ℤ) =
          (entry b (v.low k, v.column k) : ℤ) + (v.gap k : ℤ) := by exact_mod_cast hgap
      simp only [Finset.sum_insert hk]
      change (rowSum b' r : ℤ) - (rowSum a r : ℤ) =
        ((if v.low k = r then (v.gap k : ℤ) else 0) -
          (if v.high k = r then (v.gap k : ℤ) else 0)) + ∑ l ∈ S, rowNetworkDelta v l r
      dsimp only [b'] at hstep ⊢
      split_ifs at hstep ⊢ <;> omega
    · intro c
      exact (verticalSwap_columns b (v.low k) (v.high k) (v.column k) (v.rows_ne k) c).trans (hb.columns c)
    · exact hdiag.1.trans hb.main
    · exact hdiag.2.trans hb.anti
    · intro c hc
      have hk' := hc k (Finset.mem_insert_self k S)
      have hS : ∀ l ∈ S, c ≠ (v.low l, v.column l) ∧ c ≠ (v.high l, v.column l) := by
        intro l hl
        exact hc l (Finset.mem_insert_of_mem hl)
      exact (swapPlacement_outside b _ _ c hk'.1 hk'.2).trans (hb.outside_fixed c hS)

/-- A packed layer is a derangement: otherwise its two side labels would
name the same physical cell. -/
theorem LayerPacking.PackedLayers.layer_derangement {n : ℕ} {reserved : Finset (Cell n)}
    {layers : List (LayerPacking.Layer n)} (h : LayerPacking.PackedLayers reserved layers)
    (i : Fin layers.length) (e : Fin n) : (layers.get i).1 e ≠ e := by
  intro heq
  have hinj := (h.each_layer (layers.get i) (List.get_mem layers i)).1
  have hcell : LayerPacking.layerCell (layers.get i).1 (layers.get i).2 (e, true) =
      LayerPacking.layerCell (layers.get i).1 (layers.get i).2 (e, false) := by
    change ((layers.get i).1 e, (layers.get i).2 e) = (e, (layers.get i).2 e)
    rw [heq]
  have hlabels := hinj hcell
  have : true = false := congrArg Prod.snd hlabels
  contradiction

/-- The network placement interface gives exactly the physical row-pair
system needed by the simultaneous-switch theorem. -/
def LayerPacking.PackedLayers.rowPairs {n : ℕ} {reserved : Finset (Cell n)}
    {layers : List (LayerPacking.Layer n)} (h : LayerPacking.PackedLayers reserved layers)
    (a : Cell n ≃ Fin (n * n)) (gap : Fin layers.length → Fin n → ℕ)
    (hgap : ∀ i e, entry a ((layers.get i).1 e, (layers.get i).2 e) =
      entry a (e, (layers.get i).2 e) + gap i e) :
    RowNetworkPairs (Fin layers.length × Fin n) a where
  low := fun x => x.2
  high := fun x => (layers.get x.1).1 x.2
  column := fun x => (layers.get x.1).2 x.2
  rows_ne := fun x => Ne.symm (h.layer_derangement x.1 x.2)
  gap := fun x => gap x.1 x.2
  gap_at := fun x => hgap x.1 x.2
  slots_injective := by
    rintro ⟨⟨i, e⟩, side⟩ ⟨⟨j, f⟩, side'⟩ heq
    have hc : LayerPacking.sequenceCell layers (i, (e, side)) =
        LayerPacking.sequenceCell layers (j, (f, side')) := by
      simpa [LayerPacking.sequenceCell, LayerPacking.layerCell] using heq
    have hl := h.sequenceCell_injective hc
    cases hl
    rfl
  low_main := by
    intro ⟨i, e⟩
    have hm := h.support_off_diagonals _
      (LayerPacking.layerSupport_subset (layers.get i) layers (List.get_mem layers i)
        (LayerPacking.sequenceCell_mem layers i (e, false)))
    simpa [LayerPacking.sequenceCell, LayerPacking.layerCell] using hm.1
  high_main := by
    intro ⟨i, e⟩
    have hm := h.support_off_diagonals _
      (LayerPacking.layerSupport_subset (layers.get i) layers (List.get_mem layers i)
        (LayerPacking.sequenceCell_mem layers i (e, true)))
    simpa [LayerPacking.sequenceCell, LayerPacking.layerCell] using hm.1
  low_anti := by
    intro ⟨i, e⟩
    have hm := h.support_off_diagonals _
      (LayerPacking.layerSupport_subset (layers.get i) layers (List.get_mem layers i)
        (LayerPacking.sequenceCell_mem layers i (e, false)))
    simpa [LayerPacking.sequenceCell, LayerPacking.layerCell] using hm.2
  high_anti := by
    intro ⟨i, e⟩
    have hm := h.support_off_diagonals _
      (LayerPacking.layerSupport_subset (layers.get i) layers (List.get_mem layers i)
        (LayerPacking.sequenceCell_mem layers i (e, true)))
    simpa [LayerPacking.sequenceCell, LayerPacking.layerCell] using hm.2

/-- Effects of horizontal physical pairs, expressed in original coordinates
through the checked transposition of the square. -/
structure ColumnNetworkOutcome {n : ℕ} {α : Type*} [DecidableEq α]
    {a : Cell n ≃ Fin (n * n)}
    (v : RowNetworkPairs α (LayerPacking.transposePlacement a)) (S : Finset α)
    (b : Cell n ≃ Fin (n * n)) : Prop where
  columns : ∀ c, (columnSum b c : ℤ) - (columnSum a c : ℤ) = ∑ k ∈ S, rowNetworkDelta v k c
  rows : ∀ r, rowSum b r = rowSum a r
  main : mainSum b = mainSum a
  anti : antiSum b = antiSum a
  outside_fixed : ∀ c, (∀ k ∈ S,
      c ≠ (v.column k, v.low k) ∧ c ≠ (v.column k, v.high k)) →
    entry b c = entry a c

/-- Simultaneous horizontal switches preserve all rows and both diagonals;
only the displayed signed column transfers occur. -/
theorem columnNetwork_toggle_subset {n : ℕ} {α : Type*} [DecidableEq α]
    (a : Cell n ≃ Fin (n * n))
    (v : RowNetworkPairs α (LayerPacking.transposePlacement a)) (S : Finset α) :
    ∃ b : Cell n ≃ Fin (n * n), ColumnNetworkOutcome v S b := by
  obtain ⟨bt, hb⟩ := rowNetwork_toggle_subset (LayerPacking.transposePlacement a) v S
  let b := LayerPacking.transposePlacement bt
  refine ⟨b, ?_⟩
  constructor
  · intro c
    simpa [b] using hb.rows c
  · intro r
    simpa [b] using hb.columns r
  · simpa [b] using hb.main
  · simpa [b] using hb.anti
  · intro c hc
    have hc' : ∀ k ∈ S, c.swap ≠ (v.low k, v.column k) ∧ c.swap ≠ (v.high k, v.column k) := by
      intro k hk
      have h := hc k hk
      constructor
      · intro heq
        apply h.1
        have hs := congrArg Prod.swap heq
        simpa using hs
      · intro heq
        apply h.2
        have hs := congrArg Prod.swap heq
        simpa using hs
    have hh := hb.outside_fixed c.swap hc'
    rcases c with ⟨i, j⟩
    simpa [b] using hh

/-- The column network constructed by transposition supplies a physical
horizontal pair system in the actual square. -/
def LayerPacking.PackedLayers.columnPairs {n : ℕ} {reserved : Finset (Cell n)}
    {layers : List (LayerPacking.Layer n)}
    (h : LayerPacking.PackedLayers (LayerPacking.transposeCells reserved) layers)
    (a : Cell n ≃ Fin (n * n)) (gap : Fin layers.length → Fin n → ℕ)
    (hgap : ∀ i e, entry a ((layers.get i).2 e, (layers.get i).1 e) =
      entry a ((layers.get i).2 e, e) + gap i e) :
    RowNetworkPairs (Fin layers.length × Fin n) (LayerPacking.transposePlacement a) := by
  apply h.rowPairs (LayerPacking.transposePlacement a) gap
  intro i e
  simpa using hgap i e

/-- One labelled endpoint in a packed layer. -/
def layerPairSlot {n : ℕ} (layers : List (LayerPacking.Layer n))
    (k : Fin layers.length × Fin n) (side : Bool) : Cell n :=
  LayerPacking.sequenceCell layers (k.1, (k.2, side))

theorem layerPairSlot_mem {n : ℕ} (layers : List (LayerPacking.Layer n))
    (k : Fin layers.length × Fin n) (side : Bool) :
    layerPairSlot layers k side ∈ LayerPacking.layersSupport layers := by
  exact LayerPacking.layerSupport_subset (layers.get k.1) layers (List.get_mem layers k.1)
    (LayerPacking.sequenceCell_mem layers k.1 (k.2, side))

theorem transposedLayerPairSlot_mem {n : ℕ} (layers : List (LayerPacking.Layer n))
    (k : Fin layers.length × Fin n) (side : Bool) :
    (layerPairSlot layers k side).swap ∈ LayerPacking.transposeCells (LayerPacking.layersSupport layers) :=
  Finset.mem_image.mpr ⟨layerPairSlot layers k side, layerPairSlot_mem layers k side, rfl⟩

/-- The signed correction of one directed layer edge. -/
def layerTransfer {n : ℕ} (layers : List (LayerPacking.Layer n))
    (gap : Fin layers.length → Fin n → ℕ) (k : Fin layers.length × Fin n) (r : Fin n) : ℤ :=
  (if k.2 = r then (gap k.1 k.2 : ℤ) else 0) -
    (if (layers.get k.1).1 k.2 = r then (gap k.1 k.2 : ℤ) else 0)

/-- Every physical edge transfer conserves the global total exactly. -/
theorem layerTransfer_sum_zero {n : ℕ} (layers : List (LayerPacking.Layer n))
    (gap : Fin layers.length → Fin n → ℕ) (k : Fin layers.length × Fin n) :
    (∑ r : Fin n, layerTransfer layers gap k r) = 0 := by
  classical
  simp [layerTransfer, Finset.sum_sub_distrib]

/-- The same zero-total condition holds for every selected family of swaps. -/
theorem selectedTransfers_sum_zero {n : ℕ} (layers : List (LayerPacking.Layer n))
    (gap : Fin layers.length → Fin n → ℕ) (S : Finset (Fin layers.length × Fin n)) :
    (∑ r : Fin n, ∑ k ∈ S, layerTransfer layers gap k r) = 0 := by
  classical
  rw [Finset.sum_comm]
  simp [layerTransfer_sum_zero]

/-- Even physical gaps give even signed transfer at every vertex. -/
theorem selectedTransfers_even {n : ℕ} (layers : List (LayerPacking.Layer n))
    (gap : Fin layers.length → Fin n → ℕ) (S : Finset (Fin layers.length × Fin n))
    (heven : ∀ k ∈ S, 2 ∣ gap k.1 k.2) (r : Fin n) :
    (2 : ℤ) ∣ ∑ k ∈ S, layerTransfer layers gap k r := by
  apply Finset.dvd_sum
  intro k hk
  have hg : (2 : ℤ) ∣ (gap k.1 k.2 : ℤ) := by exact_mod_cast heven k hk
  unfold layerTransfer
  split_ifs <;> simp [hg]

/-- Perform arbitrary selected row and column network switches on the actual
installed square. Disjoint physical supports ensure the first pass leaves all
pairs of the second pass intact. The theorem proves every signed line effect,
keeps both diagonals and all initial reservations fixed, and preserves the
exact pool because the output remains a cell-to-rank equivalence. -/
theorem toggle_two_installed_networks {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (reserved : Finset (Cell n)) (rows cols : List (LayerPacking.Layer n))
    (hr : LayerPacking.PackedLayers reserved rows)
    (hc : LayerPacking.PackedLayers
      (LayerPacking.transposeCells (reserved ∪ LayerPacking.layersSupport rows)) cols)
    (rowGap : Fin rows.length → Fin n → ℕ)
    (colGap : Fin cols.length → Fin n → ℕ)
    (hrowGap : ∀ i e, entry a ((rows.get i).1 e, (rows.get i).2 e) =
      entry a (e, (rows.get i).2 e) + rowGap i e)
    (hcolGap : ∀ i e, entry a ((cols.get i).2 e, (cols.get i).1 e) =
      entry a ((cols.get i).2 e, e) + colGap i e)
    (Sr : Finset (Fin rows.length × Fin n))
    (Sc : Finset (Fin cols.length × Fin n)) :
    ∃ b : Cell n ≃ Fin (n * n),
      (∀ r, (rowSum b r : ℤ) - (rowSum a r : ℤ) = ∑ k ∈ Sr, layerTransfer rows rowGap k r) ∧
      (∀ c, (columnSum b c : ℤ) - (columnSum a c : ℤ) = ∑ k ∈ Sc, layerTransfer cols colGap k c) ∧
      mainSum b = mainSum a ∧ antiSum b = antiSum a ∧
      (∀ c ∈ reserved, entry b c = entry a c) ∧
      Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
  let vr := hr.rowPairs a rowGap hrowGap
  obtain ⟨br, hR⟩ := rowNetwork_toggle_subset a vr Sr
  have hcolumn_unchanged : ∀ z ∈ LayerPacking.transposeCells (LayerPacking.layersSupport cols),
      entry br z = entry a z := by
    intro z hz
    have hs := hc.transposed_support_safe z hz
    apply hR.outside_fixed z
    intro k hk
    constructor
    · intro heq
      have hmem := layerPairSlot_mem rows k false
      change (k.2, (rows.get k.1).2 k.2) ∈ LayerPacking.layersSupport rows at hmem
      apply hs.1
      apply Finset.mem_union_right reserved
      simpa [vr, LayerPacking.PackedLayers.rowPairs] using heq ▸ hmem
    · intro heq
      have hmem := layerPairSlot_mem rows k true
      change ((rows.get k.1).1 k.2, (rows.get k.1).2 k.2) ∈ LayerPacking.layersSupport rows at hmem
      apply hs.1
      apply Finset.mem_union_right reserved
      simpa [vr, LayerPacking.PackedLayers.rowPairs] using heq ▸ hmem
  have hcolGap' : ∀ i e, entry br ((cols.get i).2 e, (cols.get i).1 e) =
      entry br ((cols.get i).2 e, e) + colGap i e := by
    intro i e
    have hlow := hcolumn_unchanged _ (transposedLayerPairSlot_mem cols (i, e) false)
    have hhigh := hcolumn_unchanged _ (transposedLayerPairSlot_mem cols (i, e) true)
    change entry br ((cols.get i).2 e, e) = entry a ((cols.get i).2 e, e) at hlow
    change entry br ((cols.get i).2 e, (cols.get i).1 e) =
      entry a ((cols.get i).2 e, (cols.get i).1 e) at hhigh
    rw [hhigh, hlow]
    exact hcolGap i e
  let vc := hc.columnPairs br colGap hcolGap'
  obtain ⟨b, hC⟩ := columnNetwork_toggle_subset br vc Sc
  refine ⟨b, ?_, ?_, hC.main.trans hR.main, hC.anti.trans hR.anti, ?_, entry_range _, entry_injective _⟩
  · intro r
    rw [hC.rows r]
    exact hR.rows r
  · intro c
    have hh := hC.columns c
    rw [hR.columns c] at hh
    change (columnSum b c : ℤ) - (columnSum a c : ℤ) = ∑ k ∈ Sc, layerTransfer cols colGap k c
    exact hh
  · intro z hz
    have hRfixed : entry br z = entry a z := by
      apply hR.outside_fixed z
      intro k hk
      constructor
      · intro heq
        have hmem := layerPairSlot_mem rows k false
        change (k.2, (rows.get k.1).2 k.2) ∈ LayerPacking.layersSupport rows at hmem
        have hzmem : z ∈ LayerPacking.layersSupport rows := by
          simpa [vr, LayerPacking.PackedLayers.rowPairs] using heq ▸ hmem
        exact Finset.disjoint_left.mp hr.reserved_disjoint hz hzmem
      · intro heq
        have hmem := layerPairSlot_mem rows k true
        change ((rows.get k.1).1 k.2, (rows.get k.1).2 k.2) ∈ LayerPacking.layersSupport rows at hmem
        have hzmem : z ∈ LayerPacking.layersSupport rows := by
          simpa [vr, LayerPacking.PackedLayers.rowPairs] using heq ▸ hmem
        exact Finset.disjoint_left.mp hr.reserved_disjoint hz hzmem
    have hCfixed : entry b z = entry br z := by
      apply hC.outside_fixed z
      intro k hk
      constructor
      · intro heq
        have hmem := transposedLayerPairSlot_mem cols k false
        change ((cols.get k.1).2 k.2, k.2) ∈ LayerPacking.transposeCells (LayerPacking.layersSupport cols) at hmem
        have hzmem : z ∈ LayerPacking.transposeCells (LayerPacking.layersSupport cols) := by
          simpa [vc, LayerPacking.PackedLayers.columnPairs, LayerPacking.PackedLayers.rowPairs] using heq ▸ hmem
        exact (hc.transposed_support_safe z hzmem).1 (Finset.mem_union_left _ hz)
      · intro heq
        have hmem := transposedLayerPairSlot_mem cols k true
        change ((cols.get k.1).2 k.2, (cols.get k.1).1 k.2) ∈ LayerPacking.transposeCells (LayerPacking.layersSupport cols) at hmem
        have hzmem : z ∈ LayerPacking.transposeCells (LayerPacking.layersSupport cols) := by
          simpa [vc, LayerPacking.PackedLayers.columnPairs, LayerPacking.PackedLayers.rowPairs] using heq ▸ hmem
        exact (hc.transposed_support_safe z hzmem).1 (Finset.mem_union_left _ hz)
    exact hCfixed.trans hRfixed

/-- If actual subsets realize the requested signed transfers, both axes are
repaired simultaneously, without changing either diagonal or any original
reserved entry. The existence of these subsets is an explicit open input. -/
theorem repair_two_networks_of_selected_transfers {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (reserved : Finset (Cell n)) (rows cols : List (LayerPacking.Layer n))
    (hr : LayerPacking.PackedLayers reserved rows)
    (hc : LayerPacking.PackedLayers
      (LayerPacking.transposeCells (reserved ∪ LayerPacking.layersSupport rows)) cols)
    (rowGap : Fin rows.length → Fin n → ℕ)
    (colGap : Fin cols.length → Fin n → ℕ)
    (hrowGap : ∀ i e, entry a ((rows.get i).1 e, (rows.get i).2 e) =
      entry a (e, (rows.get i).2 e) + rowGap i e)
    (hcolGap : ∀ i e, entry a ((cols.get i).2 e, (cols.get i).1 e) =
      entry a ((cols.get i).2 e, e) + colGap i e)
    (Sr : Finset (Fin rows.length × Fin n)) (Sc : Finset (Fin cols.length × Fin n))
    (rowTarget colTarget : Fin n → ℕ)
    (hrowTransfer : ∀ r, (∑ k ∈ Sr, layerTransfer rows rowGap k r) =
      (rowTarget r : ℤ) - rowSum a r)
    (hcolTransfer : ∀ c, (∑ k ∈ Sc, layerTransfer cols colGap k c) =
      (colTarget c : ℤ) - columnSum a c) :
    ∃ b : Cell n ≃ Fin (n * n),
      (∀ r, rowSum b r = rowTarget r) ∧ (∀ c, columnSum b c = colTarget c) ∧
      mainSum b = mainSum a ∧ antiSum b = antiSum a ∧
      (∀ c ∈ reserved, entry b c = entry a c) ∧
      Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
  obtain ⟨b, hrows, hcols, hm, ha, hfixed, hpool, hinj⟩ :=
    toggle_two_installed_networks a reserved rows cols hr hc rowGap colGap
      hrowGap hcolGap Sr Sc
  refine ⟨b, ?_, ?_, hm, ha, hfixed, hpool, hinj⟩
  · intro r
    have hh := hrows r
    rw [hrowTransfer r] at hh
    exact_mod_cast (show (rowSum b r : ℤ) = (rowTarget r : ℤ) by omega)
  · intro c
    have hh := hcols c
    rw [hcolTransfer c] at hh
    exact_mod_cast (show (columnSum b c : ℤ) = (colTarget c : ℤ) by omega)

/-- A completed pre-switch placement with prime diagonals and actual selected
subsets satisfying the displayed transfers yields the public square. No
assertion is made here that those subsets or the input placement exist. -/
theorem square_of_selected_network_transfers {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (reserved : Finset (Cell n)) (rows cols : List (LayerPacking.Layer n))
    (hr : LayerPacking.PackedLayers reserved rows)
    (hc : LayerPacking.PackedLayers
      (LayerPacking.transposeCells (reserved ∪ LayerPacking.layersSupport rows)) cols)
    (rowGap : Fin rows.length → Fin n → ℕ)
    (colGap : Fin cols.length → Fin n → ℕ)
    (hrowGap : ∀ i e, entry a ((rows.get i).1 e, (rows.get i).2 e) =
      entry a (e, (rows.get i).2 e) + rowGap i e)
    (hcolGap : ∀ i e, entry a ((cols.get i).2 e, (cols.get i).1 e) =
      entry a ((cols.get i).2 e, e) + colGap i e)
    (Sr : Finset (Fin rows.length × Fin n)) (Sc : Finset (Fin cols.length × Fin n))
    (rowTarget colTarget : Fin n → ℕ)
    (hrowTransfer : ∀ r, (∑ k ∈ Sr, layerTransfer rows rowGap k r) =
      (rowTarget r : ℤ) - rowSum a r)
    (hcolTransfer : ∀ c, (∑ k ∈ Sc, layerTransfer cols colGap k c) =
      (colTarget c : ℤ) - columnSum a c)
    (hrowPrime : ∀ r, Nat.Prime (rowTarget r))
    (hcolPrime : ∀ c, Nat.Prime (colTarget c))
    (hmain : Nat.Prime (mainSum a)) (hanti : Nat.Prime (antiSum a)) : HasSquare n := by
  obtain ⟨b, hrows, hcols, hm, ha, _, _, _⟩ :=
    repair_two_networks_of_selected_transfers a reserved rows cols hr hc rowGap colGap
      hrowGap hcolGap Sr Sc rowTarget colTarget hrowTransfer hcolTransfer
  refine ⟨b, ?_⟩
  exact ⟨fun r => (hrows r).symm ▸ hrowPrime r,
    fun c => (hcols c).symm ▸ hcolPrime c, hm.symm ▸ hmain, ha.symm ▸ hanti⟩

end
end Sude
