import Sude.LayerPackingConcatenate
import Sude.LayerTranspose

/-! Reorder an interleaved bridge/seed/wide/growth packing into all row layers
followed by all column layers, without moving any physical cells. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096

private theorem fw_transpose_union {n : ℕ} (a b : Finset (Cell n)) :
    LayerPacking.transposeCells (a ∪ b) = LayerPacking.transposeCells a ∪ LayerPacking.transposeCells b := by
  simp [LayerPacking.transposeCells, Finset.image_union]

/-- Reorder two already packed row/column batches. The second row batch
avoids the earlier column batch, so that earlier columns can be packed after
both row batches. -/
theorem fw_reorder_two_layer_batches {n : ℕ} (base : Finset (Cell n))
    (ra ca rb cb : List (LayerPacking.Layer n))
    (hra : LayerPacking.PackedLayers base ra)
    (hca : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (base ∪ LayerPacking.layersSupport ra)) ca)
    (hrb : LayerPacking.PackedLayers
      ((base ∪ LayerPacking.layersSupport ra) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport ca)) rb)
    (hcb : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (((base ∪ LayerPacking.layersSupport ra) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport ca)) ∪
        LayerPacking.layersSupport rb)) cb) :
    LayerPacking.PackedLayers base (ra ++ rb) ∧
    LayerPacking.PackedLayers (LayerPacking.transposeCells
      (base ∪ LayerPacking.layersSupport (ra ++ rb))) (ca ++ cb) := by
  have hnewRows : LayerPacking.PackedLayers (base ∪ LayerPacking.layersSupport ra) rb :=
    hrb.weaken_reservation (by intro z hz; exact Finset.mem_union_left _ hz)
  have hrow := hra.append_packed hnewRows
  have hcross : Disjoint (LayerPacking.transposeCells (LayerPacking.layersSupport rb))
      (LayerPacking.layersSupport ca) := by
    apply Finset.disjoint_left.mpr
    intro z hz hca'
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    have hx' : x ∈ LayerPacking.transposeCells (LayerPacking.layersSupport ca) :=
      Finset.mem_image.mpr ⟨x.swap, hca', by simp⟩
    exact Finset.disjoint_left.mp hrb.reserved_disjoint (Finset.mem_union_right _ hx') hx
  have hca' := hca.extend_reservation hcross
  have hca'' : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (base ∪ LayerPacking.layersSupport (ra ++ rb))) ca := by
    simpa [LayerPacking.layersSupport_append, fw_transpose_union, Finset.union_assoc] using hca'
  have hcb' : LayerPacking.PackedLayers
      (LayerPacking.transposeCells (base ∪ LayerPacking.layersSupport (ra ++ rb)) ∪
        LayerPacking.layersSupport ca) cb := by
    simpa [LayerPacking.layersSupport_append, fw_transpose_union, Finset.union_assoc,
      Finset.union_comm, Finset.union_left_comm] using hcb
  exact ⟨hrow, hca''.append_packed hcb'⟩

/-- Normalize the four actual interleaved FW layer families. The full
rectangle reservation remains untouched; this theorem only repackages
existing geometric proofs and makes no assertion about entries or switches. -/
theorem fw_joint_layer_packing {n : ℕ} (rect : Finset (Cell n))
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : LayerPacking.PackedLayers rect br)
    (hbc : LayerPacking.PackedLayers (LayerPacking.transposeCells (rect ∪ LayerPacking.layersSupport br)) bc)
    (hsr : LayerPacking.PackedLayers
      ((rect ∪ LayerPacking.layersSupport br) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport bc)) sr)
    (hsc : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (((rect ∪ LayerPacking.layersSupport br) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport bc)) ∪
        LayerPacking.layersSupport sr)) sc)
    (hwr : LayerPacking.PackedLayers
      ((((rect ∪ LayerPacking.layersSupport br) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport bc)) ∪
        LayerPacking.layersSupport sr) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport sc)) wr)
    (hwc : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (((((rect ∪ LayerPacking.layersSupport br) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport bc)) ∪
        LayerPacking.layersSupport sr) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport sc)) ∪
        LayerPacking.layersSupport wr)) wc)
    (hgr : LayerPacking.PackedLayers
      ((((((rect ∪ LayerPacking.layersSupport br) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport bc)) ∪
        LayerPacking.layersSupport sr) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport sc)) ∪
        LayerPacking.layersSupport wr) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport wc)) gr)
    (hgc : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (((((((rect ∪ LayerPacking.layersSupport br) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport bc)) ∪
        LayerPacking.layersSupport sr) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport sc)) ∪
        LayerPacking.layersSupport wr) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport wc)) ∪
        LayerPacking.layersSupport gr)) gc) :
    LayerPacking.PackedLayers rect (((br ++ sr) ++ wr) ++ gr) ∧
    LayerPacking.PackedLayers (LayerPacking.transposeCells
      (rect ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr))) (((bc ++ sc) ++ wc) ++ gc) := by
  obtain ⟨hr1, hc1⟩ := fw_reorder_two_layer_batches rect br bc sr sc hbr hbc hsr hsc
  have hwr' : LayerPacking.PackedLayers
      ((rect ∪ LayerPacking.layersSupport (br ++ sr)) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport (bc ++ sc))) wr := by
    simpa [LayerPacking.layersSupport_append, fw_transpose_union, Finset.union_assoc,
      Finset.union_comm, Finset.union_left_comm] using hwr
  have hwc' : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (((rect ∪ LayerPacking.layersSupport (br ++ sr)) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport (bc ++ sc))) ∪ LayerPacking.layersSupport wr)) wc := by
    simpa [LayerPacking.layersSupport_append, fw_transpose_union, Finset.union_assoc,
      Finset.union_comm, Finset.union_left_comm] using hwc
  obtain ⟨hr2, hc2⟩ := fw_reorder_two_layer_batches rect (br ++ sr) (bc ++ sc) wr wc hr1 hc1 hwr' hwc'
  have hgr' : LayerPacking.PackedLayers
      ((rect ∪ LayerPacking.layersSupport ((br ++ sr) ++ wr)) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport ((bc ++ sc) ++ wc))) gr := by
    simpa [LayerPacking.layersSupport_append, fw_transpose_union, Finset.union_assoc,
      Finset.union_comm, Finset.union_left_comm] using hgr
  have hgc' : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (((rect ∪ LayerPacking.layersSupport ((br ++ sr) ++ wr)) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport ((bc ++ sc) ++ wc))) ∪ LayerPacking.layersSupport gr)) gc := by
    simpa [LayerPacking.layersSupport_append, fw_transpose_union, Finset.union_assoc,
      Finset.union_comm, Finset.union_left_comm] using hgc
  exact fw_reorder_two_layer_batches rect ((br ++ sr) ++ wr) ((bc ++ sc) ++ wc) gr gc hr2 hc2 hgr' hgc'

end
end Sude
