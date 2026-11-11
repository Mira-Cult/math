import Sude.FWGrowthRectangleChoice
import Sude.DiagonalStageInvoice
import Sude.FWBridgeRectangleInvoice
import Sude.FWWideOffsetPairIncidence

/-! Balanced-choice rectangle pair invoices for FW bridge and wide stages.
Ordinary network contributions and concentration are not asserted. -/

namespace Sude
noncomputable section

/-- The stage's squared rectangle-pair incidence on a labelled line. -/
def fwLabelledDiagonalInvoice {n L : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (labels : Fin (4 * 6) → Fin L)
    (line : Cell n → Prop) : ℝ :=
  ∑ i, ∑ pair : Fin 2, (rectanglePairWeight hs choice line (labels i, pair)) ^ 2

/-- A balanced choice gives exactly twelve incidences on each diagonal.
The labels are supplied injectively; the numerical identity itself only uses
the balanced-choice equation. -/
theorem fw_labelled_balanced_diagonal_invoice {n L : ℕ} (hs : 2 * L + 1 ≤ n)
    (hL : 3 ≤ L) (choice : Fin L → Bool) (labels : Fin (4 * 6) → Fin L)
    (_hinj : Function.Injective labels)
    (hchoice : ∀ i, choice (labels i) = decide (i.val < 2 * 6)) :
    fwLabelledDiagonalInvoice hs choice labels (fun c => c ∈ mainCells n) = 12 ∧
      fwLabelledDiagonalInvoice hs choice labels (fun c => c ∈ antiCells n) = 12 := by
  constructor
  · calc
      _ = (((Finset.univ : Finset (Fin (4 * 6))).filter fun i => i.val < 2 * 6).card : ℝ) := by
        simp only [fwLabelledDiagonalInvoice, Fin.sum_univ_two, rectanglePairWeight_main hs hL]
        simp [hchoice]
      _ = 12 := by rw [(bridgeDiagonal_index_counts 6).1]; norm_num
  · calc
      _ = (((Finset.univ : Finset (Fin (4 * 6))).filter fun i => ¬ i.val < 2 * 6).card : ℝ) := by
        simp only [fwLabelledDiagonalInvoice, Fin.sum_univ_two, rectanglePairWeight_anti hs hL]
        simp [hchoice]
      _ = 12 := by rw [(bridgeDiagonal_index_counts 6).2]; norm_num

/-- The actual joint FW choice pays both bridge diagonal invoices at every
bridge stage; the supplied fallback includes any later growth choice. -/
theorem fw_bridge_balanced_diagonal_invoice {n L P : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hgrowth : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (otherChoice : Fin L → Bool) (j : Fin 5) :
    let choice := fwBridgeSeedWideGrowthChoice hrect hseed hwide hgrowth otherChoice
    let labels := fun i : Fin (4 * 6) => bridgeDiagonalRectangle hrect (finProdFinEquiv (j,i))
    fwLabelledDiagonalInvoice hs choice labels (fun c => c ∈ mainCells n) = 12 ∧
      fwLabelledDiagonalInvoice hs choice labels (fun c => c ∈ antiCells n) = 12 := by
  dsimp only
  apply fw_labelled_balanced_diagonal_invoice hs hL
  · intro a b h
    have hp := finProdFinEquiv.injective ((bridgeDiagonalRectangle_injective hrect) h)
    exact congrArg Prod.snd hp
  · exact fwBridgeSeedWideGrowthChoice_bridge hrect hseed hwide hgrowth otherChoice j

/-- The actual joint FW choice also pays both invoices at each wide stage;
wide rectangle labels include their 504-label offset. -/
theorem fw_wide_balanced_diagonal_invoice {n L P : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hgrowth : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (otherChoice : Fin L → Bool)
    (j : Fin (3 * (n / 450))) :
    let choice := fwBridgeSeedWideGrowthChoice hrect hseed hwide hgrowth otherChoice
    let labels := fun i : Fin (4 * 6) => fwWideRectangle hwide (finProdFinEquiv (j,i))
    fwLabelledDiagonalInvoice hs choice labels (fun c => c ∈ mainCells n) = 12 ∧
      fwLabelledDiagonalInvoice hs choice labels (fun c => c ∈ antiCells n) = 12 := by
  dsimp only
  apply fw_labelled_balanced_diagonal_invoice hs hL
  · intro a b h
    have hp := finProdFinEquiv.injective ((fwWideRectangle_injective hwide) h)
    exact congrArg Prod.snd hp
  · exact fwBridgeSeedWideGrowthChoice_wide hrect hseed hwide hgrowth otherChoice j


/-- The balanced bridge invoice holds on its actual reindexed physical
rectangle pair cells, independently of the ordinary network cells. -/
theorem fw_bridge_physical_balanced_diagonal_invoice {n L P : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hgrowth : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (otherChoice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (j : Fin 5) :
    let choice := fwBridgeSeedWideGrowthChoice hrect hseed hwide hgrowth otherChoice
    let w := fun line : Cell n → Prop => ∑ i : Fin (4 * 6), ∑ pair : Fin 2,
      (physicalPairLineWeight (fwBridgePhysicalPairCells hrect hs choice rows cols hr hc) line
        (j, fwPrefixToControllerPair n (prefixDiagonalPairIndex
          (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (i,pair)))) ^ 2
    w (fun c => c ∈ mainCells n) = 12 ∧ w (fun c => c ∈ antiCells n) = 12 := by
  dsimp only
  have h := fw_bridge_balanced_diagonal_invoice hrect hseed hwide hgrowth hs hL otherChoice j
  dsimp only at h
  constructor
  · simp_rw [fw_bridge_reindexed_rectangle_pair_weight]
    simpa [fwLabelledDiagonalInvoice, prefixRectanglePairSlot, bridgeDiagonalRectangle] using h.1
  · simp_rw [fw_bridge_reindexed_rectangle_pair_weight]
    simpa [fwLabelledDiagonalInvoice, prefixRectanglePairSlot, bridgeDiagonalRectangle] using h.2

/-- The corresponding balanced invoice on the actual offset wide rectangle
pair cells, independently of the ordinary network cells. -/
theorem fw_wide_physical_balanced_diagonal_invoice {n L P : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hgrowth : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (otherChoice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (j : Fin (3 * (n / 450))) :
    let choice := fwBridgeSeedWideGrowthChoice hrect hseed hwide hgrowth otherChoice
    let w := fun line : Cell n → Prop => ∑ i : Fin (4 * 6), ∑ pair : Fin 2,
      (physicalPairLineWeight (fwWidePhysicalPairCells hwide hs choice rows cols hr hc) line
        (j, fwPrefixToControllerPair n (prefixDiagonalPairIndex
          (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega) (i,pair)))) ^ 2
    w (fun c => c ∈ mainCells n) = 12 ∧ w (fun c => c ∈ antiCells n) = 12 := by
  dsimp only
  have h := fw_wide_balanced_diagonal_invoice hrect hseed hwide hgrowth hs hL otherChoice j
  dsimp only at h
  constructor
  · simp_rw [fw_wide_reindexed_rectangle_pair_weight]
    simpa [fwLabelledDiagonalInvoice, fwWideOffsetPairSlot] using h.1
  · simp_rw [fw_wide_reindexed_rectangle_pair_weight]
    simpa [fwLabelledDiagonalInvoice, fwWideOffsetPairSlot] using h.2

end
end Sude
