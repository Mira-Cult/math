import Sude.FWWidePhysicalSlots
import Sude.FWInstalledGap

/-! Map a fixed wide network edge to the same selected block and physical
pair in the supplied square. No selection, trace, or disjointness is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096

/-- One stage, graph edge, network and endpoint side in the actual wide role map. -/
def fwWideEdgeRole (n : ℕ) (j : Fin (3 * (n / 450))) (k : Fin 3) (e : Fin n)
    (network side : Bool) : FWWideInputs n :=
  Sum.inr ((j, (k, e)), (network, side))

/-- The selected flat block used by both networks and both endpoint sides. -/
def fwWideEdgeBlock {n : ℕ} (blocks : List DoublePair)
    (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (j : Fin (3 * (n / 450))) (k : Fin 3) (e : Fin n) : Fin blocks.length :=
  Fin.cast hlen.symm (fwWideFlatSlot n (fwWideEdgeRole n j k e false false)).1

/-- Flattening an ordinary edge names the same block for all four sides. -/
theorem fwWideEdgeRole_flat {n : ℕ} (blocks : List DoublePair)
    (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (j : Fin (3 * (n / 450))) (k : Fin 3) (e : Fin n) (network side : Bool) :
    (Fin.cast hlen.symm (fwWideFlatSlot n (fwWideEdgeRole n j k e network side)).1,
      (fwWideFlatSlot n (fwWideEdgeRole n j k e network side)).2) =
      (fwWideEdgeBlock blocks hlen j k e, bridgeOrdinarySide (network, side)) := by
  rfl

/-- The inverse flattening used by the wide installation theorem maps that
block's ordinary endpoint back to its actual fixed-edge cell. -/
theorem fwWideEdgeCell_eq {n L : ℕ} (blocks : List DoublePair)
    (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (j : Fin (3 * (n / 450))) (k : Fin 3) (e : Fin n) (network side : Bool) :
    fwWidePhysicalCells hwide hs choice rows cols hr hc
      ((Equiv.ofBijective (fwWideFlatSlot n) (fwWideFlatSlot_bijective n)).symm
        (Fin.cast hlen (fwWideEdgeBlock blocks hlen j k e), bridgeOrdinarySide (network, side))) =
    fwWidePhysicalCells hwide hs choice rows cols hr hc (fwWideEdgeRole n j k e network side) := by
  congr 1
  apply (Equiv.ofBijective (fwWideFlatSlot n) (fwWideFlatSlot_bijective n)).symm_apply_eq.mpr
  apply Prod.ext
  · simp [fwWideEdgeBlock, fwWideFlatSlot, fwWideEdgeRole, fwWideControllerSlot, bridgeOrdinarySlot]
  · rfl

/-- The selected-block cell map used by the wide placement interface. -/
def fwWideSelectedCells {n L : ℕ} (blocks : List DoublePair)
    (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (x : Fin blocks.length × Fin 4) : Cell n :=
  fwWidePhysicalCells hwide hs choice rows cols hr hc
    ((Equiv.ofBijective (fwWideFlatSlot n) (fwWideFlatSlot_bijective n)).symm
      (Fin.cast hlen x.1, x.2))

/-- The selected block gap applies to both physical network pairs for a
fixed stage and edge, including its supplied numeric bounds. -/
theorem fw_wide_edge_physical_gap {n L : ℕ} (X : ℝ) (blocks : List DoublePair)
    (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (a : Cell n ≃ Fin (n * n))
    (hgap : ∀ i : Fin blocks.length, ∃ gap : ℕ, 0 < gap ∧ gap % 2 = 0 ∧
        entry a (fwWideSelectedCells blocks hlen hwide hs choice rows cols hr hc (i, 1)) =
          entry a (fwWideSelectedCells blocks hlen hwide hs choice rows cols hr hc (i, 0)) + gap ∧
        entry a (fwWideSelectedCells blocks hlen hwide hs choice rows cols hr hc (i, 2)) =
          entry a (fwWideSelectedCells blocks hlen hwide hs choice rows cols hr hc (i, 3)) + gap ∧
        (2 / 3 : ℝ) * X ≤ (gap : ℝ) ∧ (gap : ℝ) < X)
    (j : Fin (3 * (n / 450))) (k : Fin 3) (e : Fin n) :
    ∃ gap : ℕ, 0 < gap ∧ gap % 2 = 0 ∧
      (∀ network : Bool,
        entry a (fwWidePhysicalCells hwide hs choice rows cols hr hc (fwWideEdgeRole n j k e network true)) =
        entry a (fwWidePhysicalCells hwide hs choice rows cols hr hc (fwWideEdgeRole n j k e network false)) + gap) ∧
      (2 / 3 : ℝ) * X ≤ (gap : ℝ) ∧ (gap : ℝ) < X := by
  obtain ⟨gap, hpos, heven, hfirst, hsecond, hlo, hhi⟩ := hgap (fwWideEdgeBlock blocks hlen j k e)
  refine ⟨gap, hpos, heven, ?_, hlo, hhi⟩
  intro network
  cases network
  · have ht := fwWideEdgeCell_eq blocks hlen hwide hs choice rows cols hr hc j k e false true
    have hf := fwWideEdgeCell_eq blocks hlen hwide hs choice rows cols hr hc j k e false false
    simp only [bridgeOrdinarySide, Bool.false_eq_true, ↓reduceIte] at ht hf
    simp only [fwWideSelectedCells] at hfirst
    rw [ht, hf] at hfirst
    exact hfirst
  · have ht := fwWideEdgeCell_eq blocks hlen hwide hs choice rows cols hr hc j k e true true
    have hf := fwWideEdgeCell_eq blocks hlen hwide hs choice rows cols hr hc j k e true false
    simp only [bridgeOrdinarySide, ↓reduceIte, Bool.false_eq_true] at ht hf
    simp only [fwWideSelectedCells] at hsecond
    rw [ht, hf] at hsecond
    exact hsecond

/-- Both wide network pairs lie on the supplied graph edge, with the row
and column coordinates of their actual packed layers. -/
theorem fw_wide_edge_physical_coordinates {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (p : Fin 3 → Equiv.Perm (Fin n))
    (hends : ∀ (j : Fin (3 * (n / 450))) (k : Fin 3) (e : Fin n),
      (rows.get (bridgeStageLayerIndex hr j k)).1 e = p k e ∧
      (cols.get (bridgeStageLayerIndex hc j k)).1 e = p k e)
    (j : Fin (3 * (n / 450))) (k : Fin 3) (e : Fin n) (side : Bool) :
    fwWidePhysicalCells hwide hs choice rows cols hr hc (fwWideEdgeRole n j k e false side) =
      ((if side then p k e else e), (rows.get (bridgeStageLayerIndex hr j k)).2 e) ∧
    fwWidePhysicalCells hwide hs choice rows cols hr hc (fwWideEdgeRole n j k e true side) =
      ((cols.get (bridgeStageLayerIndex hc j k)).2 e, (if side then p k e else e)) := by
  have hrow := (hends j k e).1
  have hcol := (hends j k e).2
  simp [bridgeStageLayerIndex] at hrow hcol
  cases side <;>
    simp [fwWidePhysicalCells, fwWideEdgeRole, fwWideOrdinaryCells, fwWideLayerIndex,
      bridgeStageLayerIndex, LayerPacking.sequenceCell, LayerPacking.layerCell, hrow, hcol]

end
end Sude
