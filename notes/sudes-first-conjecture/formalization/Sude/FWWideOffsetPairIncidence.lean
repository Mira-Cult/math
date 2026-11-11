import Sude.FWControllerStageReindex
import Sude.RectanglePairInvoice

/-! Wide rectangle pair slots and their actual reindexed physical incidences.
No line-mass upper bound, balanced diagonal choice, or packing is asserted. -/
namespace Sude
noncomputable section

/-- The actual offset wide rectangle and pair for each stage-local label. -/
def fwWideOffsetPairSlot {J L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + J * (4 * 6) ≤ L) :
    ((Fin J × Fin (4 * 6)) × Fin 2) → Fin L × Fin 2 :=
  fun x => (fwWideRectangle hwide (finProdFinEquiv x.1), x.2)

/-- Distinct stage/rectangle/pair labels name distinct offset pair slots. -/
theorem fwWideOffsetPairSlot_injective {J L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + J * (4 * 6) ≤ L) :
    Function.Injective (fwWideOffsetPairSlot hwide) := by
  rintro ⟨i, p⟩ ⟨j, q⟩ h
  have hi : i = j := finProdFinEquiv.injective
    (fwWideRectangle_injective hwide (congrArg Prod.fst h))
  have hp : p = q := congrArg Prod.snd h
  exact Prod.ext hi hp

/-- A reindexed physical wide diagonal-tag pair has exactly the incidence
weight of its offset packed rectangle pair, for an arbitrary line predicate. -/
theorem fw_wide_reindexed_rectangle_pair_weight {n L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (line : Cell n → Prop) (j : Fin (3 * (n / 450))) (rect : Fin (4 * 6)) (pair : Fin 2) :
    physicalPairLineWeight (fwWidePhysicalPairCells hwide hs choice rows cols hr hc) line
      (j, fwPrefixToControllerPair n
        (prefixDiagonalPairIndex (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (rect,pair))) =
    rectanglePairWeight hs choice line (fwWideOffsetPairSlot hwide ((j,rect),pair)) := by
  classical
  unfold physicalPairLineWeight rectanglePairWeight fwWideOffsetPairSlot
  rw [fw_wide_reindexed_diagonal_cell hwide hs choice rows cols hr hc j rect pair false,
      fw_wide_reindexed_diagonal_cell hwide hs choice rows cols hr hc j rect pair true]

end
end Sude
