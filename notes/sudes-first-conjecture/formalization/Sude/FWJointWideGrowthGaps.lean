import Sude.FWPreservedWideEdgeRoles
import Sude.BTGrowingOffsetPhysical

/-! Recover ordinary layer orientations from the actual wide and growth
placement equations. No simultaneous switching or crossing is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 8192

/-- The per-edge wide gaps on one square orient every wide row and column
layer pair, including all stage/edge indices. -/
theorem fw_wide_layers_ordered {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3) (a : Cell n ≃ Fin (n*n))
    (hwideGap : ∀ (j : Fin (3 * (n / 450))) (k : Fin 3) (e : Fin n),
      ∃ gap : ℕ, 0 < gap ∧ gap % 2 = 0 ∧
        (∀ network : Bool,
          entry a (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j k e network true)) =
          entry a (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j k e network false)) + gap) ∧
        (2 / 3 : ℝ) * (poolMaximum n : ℝ) ≤ (gap : ℝ) ∧ (gap : ℝ) < poolMaximum n) :
    (∀ (i : Fin wr.length) (e : Fin n),
      entry a (e, (wr.get i).2 e) ≤ entry a ((wr.get i).1 e, (wr.get i).2 e)) ∧
    (∀ (i : Fin wc.length) (e : Fin n),
      entry a ((wc.get i).2 e, e) ≤ entry a ((wc.get i).2 e, (wc.get i).1 e)) := by
  constructor
  · intro i e
    let jk : Fin (3 * (n / 450)) × Fin 3 := finProdFinEquiv.symm (Fin.cast hwr i)
    obtain ⟨gap, _, _, hpair, _, _⟩ := hwideGap jk.1 jk.2 e
    have hp := hpair false
    have hi : Fin.cast hwr.symm (finProdFinEquiv jk) = i := by
      change Fin.cast hwr.symm (finProdFinEquiv (finProdFinEquiv.symm (Fin.cast hwr i))) = i
      rw [Equiv.apply_symm_apply, Fin.cast_cast, Fin.cast_eq_self]
    simp only [fwWidePhysicalCells, fwWideEdgeRole, Sum.elim_inr, fwWideOrdinaryCells,
      Bool.false_eq_true, ↓reduceIte, fwWideLayerIndex, LayerPacking.sequenceCell,
      LayerPacking.layerCell, hi] at hp
    omega
  · intro i e
    let jk : Fin (3 * (n / 450)) × Fin 3 := finProdFinEquiv.symm (Fin.cast hwc i)
    obtain ⟨gap, _, _, hpair, _, _⟩ := hwideGap jk.1 jk.2 e
    have hp := hpair true
    have hi : Fin.cast hwc.symm (finProdFinEquiv jk) = i := by
      change Fin.cast hwc.symm (finProdFinEquiv (finProdFinEquiv.symm (Fin.cast hwc i))) = i
      rw [Equiv.apply_symm_apply, Fin.cast_cast, Fin.cast_eq_self]
    simp only [fwWidePhysicalCells, fwWideEdgeRole, Sum.elim_inr, fwWideOrdinaryCells,
      ↓reduceIte, fwWideLayerIndex, LayerPacking.sequenceCell,
      LayerPacking.layerCell, hi, Bool.false_eq_true, ↓reduceIte, Prod.swap_prod_mk] at hp
    omega

/-- The installed trace equations orient all ordinary growth row and column
layer pairs on the same square. -/
theorem fw_growth_layers_ordered {n L : ℕ}
    {stages : List BTSelectedStage} (offset : ℕ)
    (hoff : offset + stages.length * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (gr gc : List (LayerPacking.Layer n))
    (hgr : gr.length = stages.length * 3) (hgc : gc.length = stages.length * 3)
    (a : Cell n ≃ Fin (n*n))
    (hrow : ∀ (i : Fin (stages.length * 3)) (e : Fin n),
      entry a (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inl (i, (e, true))))) =
      entry a (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inl (i, (e, false))))) +
        variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages rfl j).gap) rfl i e)
    (hcol : ∀ (i : Fin (stages.length * 3)) (e : Fin n),
      entry a (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inr (i, (e, true))))) =
      entry a (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc (Sum.inr (Sum.inr (i, (e, false))))) +
        variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages rfl j).gap) rfl i e) :
    (∀ (i : Fin gr.length) (e : Fin n),
      entry a (e, (gr.get i).2 e) ≤ entry a ((gr.get i).1 e, (gr.get i).2 e)) ∧
    (∀ (i : Fin gc.length) (e : Fin n),
      entry a ((gc.get i).2 e, e) ≤ entry a ((gc.get i).2 e, (gc.get i).1 e)) := by
  constructor
  · intro i e
    have hp := hrow (Fin.cast hgr i) e
    simp only [btGrowingOffsetCells, Fin.cast_cast, Fin.cast_eq_self, LayerPacking.sequenceCell,
      LayerPacking.layerCell, Bool.false_eq_true, ↓reduceIte] at hp
    omega
  · intro i e
    have hp := hcol (Fin.cast hgc i) e
    simp only [btGrowingOffsetCells, Fin.cast_cast, Fin.cast_eq_self, LayerPacking.sequenceCell,
      LayerPacking.layerCell, Bool.false_eq_true, ↓reduceIte, Prod.swap_prod_mk] at hp
    omega

end
end Sude
