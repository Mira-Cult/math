import Sude.PrefixLStage0Values
import Sude.FC2KExpanderPhysical

/-! Install the actually certified first L stage in physical cells. -/
namespace Sude.GeneratedPrefix.LStage0
noncomputable section

theorem ordinaryFit (n : ℕ) : (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) := by omega
theorem diagonalFit (n : ℕ) : (4 * 6) * 2 ≤ 6 * (n + 8) := by omega
theorem rectangleFit : 1 * (4 * 6) ≤ 24 := by decide
def rectangleChoice : Fin 24 → Bool := fun _ => false
theorem squareFit {n : ℕ} (hn : 2001 ≤ n) : 2 * 24 + 1 ≤ n := by omega

def rectangleCells {n : ℕ} (hn : 2001 ≤ n) : Finset (Cell n) :=
  allocatedBridgeRectangleSupport rectangleFit (squareFit hn) rectangleChoice

/-- For every order in the L band, the first certified stage fills all of
its 24 diagonal rectangles and both degree-six physical networks. The only
analytic input is the explicit lower prime-index estimate used to put these
certified primes in the prescribed pool. This single binary stage does not
provide a complete routing radius or prove a tail route. -/
theorem install_certified_stage (lower : RSIndexLower) {n : ℕ}
    (hn : 2001 ≤ n) (hnmax : n ≤ 2400) (a : Cell n ≃ Fin (n * n)) :
    ∃ (p : Fin 3 → Equiv.Perm (Fin n))
      (rows cols : List (LayerPacking.Layer n))
      (hrlen : rows.length = 1 * 3) (hclen : cols.length = 1 * 3)
      (b : Cell n ≃ Fin (n * n)),
      (∀ i v, p i v ≠ v) ∧
      (∀ S : Finset (Fin n), 199 * min S.card (n - S.card) ≤
        200 * (cutEdges (fun e : Fin 3 × Fin n => e.2)
          (fun e => p e.1 e.2) S).card) ∧
      rows.map Prod.fst = bridgeRepeatedPermutations 1 p ∧
      cols.map Prod.fst = bridgeRepeatedPermutations 1 p ∧
      LayerPacking.PackedLayers (rectangleCells hn) rows ∧
      LayerPacking.PackedLayers (LayerPacking.transposeCells
        (rectangleCells hn ∪ LayerPacking.layersSupport rows)) cols ∧
      Disjoint (LayerPacking.layersSupport rows)
        (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∧
      (∀ x : Fin (1 * (4 * 6)) × Fin 4,
        entry b (packedRectangleCorner (squareFit hn) rectangleChoice
          (Fin.castLE rectangleFit x.1, x.2)) =
            (allocatorValues lower (by omega) hnmax (prefixRectangleInput (diagonalFit n) x)).val) ∧
      (∀ x, entry b (LayerPacking.sequenceCell rows x) =
        (allocatorValues lower (by omega) hnmax (prefixNetworkInput (ordinaryFit n) hrlen 0 x)).val) ∧
      (∀ x, entry b (LayerPacking.sequenceCell cols x).swap =
        (allocatorValues lower (by omega) hnmax (prefixNetworkInput (ordinaryFit n) hclen 1 x)).val) ∧
      ((rectangleCells hn ∪ (LayerPacking.layersSupport rows ∪
          LayerPacking.transposeCells (LayerPacking.layersSupport cols))).image (entry b) =
        (Finset.univ : Finset ((Fin 1 × Fin (6 * (n + 8))) × Bool)).image
          (fun x => (allocatorValues lower (by omega) hnmax x).val)) ∧
      ((rectangleCells hn ∪ (LayerPacking.layersSupport rows ∪
          LayerPacking.transposeCells (LayerPacking.layersSupport cols))).image (entry b)).card =
        2 * (6 * (n + 8)) ∧
      (∀ i e, entry b ((rows.get i).1 e, (rows.get i).2 e) =
        entry b (e, (rows.get i).2 e) + prefixNetworkGap hrlen i e) ∧
      (∀ i e, entry b ((cols.get i).2 e, (cols.get i).1 e) =
        entry b ((cols.get i).2 e, e) + prefixNetworkGap hclen i e) := by
  have hcap : 4 * ((0 + 2) + 2 * (1 * 3) + 2 * (1 * 3)) + 8 < n := by omega
  obtain ⟨p, rows, cols, hrlen, hclen, b, hder, hexp, hrmap, hcmap, hrpack, hcpack,
    hdisjoint, hrect, hrplaced, hcplaced, hrgap, hcgap, _⟩ :=
    fc2k_install_expanding_prefix hn (ordinaryFit n) (diagonalFit n) rectangleFit
      (squareFit hn) rectangleChoice (allocatorValues lower (by omega) hnmax)
      (allocatorValues_injective lower (by omega) hnmax)
      (allocatorValues_gap lower (by omega) hnmax) ∅ (by simp) ∅
      (by simp [LayerPacking.rowUsed]) (by simp [LayerPacking.colUsed]) hcap a (by simp) (by simp)
  have hpl : (bridgeRepeatedPermutations 1 p).length = 1 * 3 :=
    bridgeRepeatedPermutations_length p
  have hrlen' : rows.length = (bridgeRepeatedPermutations 1 p).length := hrlen.trans hpl.symm
  have hclen' : cols.length = (bridgeRepeatedPermutations 1 p).length := hclen.trans hpl.symm
  have hrplaced' : ∀ x, entry b (LayerPacking.sequenceCell rows x) =
      (allocatorValues lower (by omega) hnmax
        (prefixNetworkInput (ordinaryFit n) hpl 0 (Fin.cast hrlen' x.1, x.2))).val := by
    intro x
    simpa only [prefixNetworkInput_cast] using hrplaced x
  have hcplaced' : ∀ x, entry b (LayerPacking.sequenceCell cols x).swap =
      (allocatorValues lower (by omega) hnmax
        (prefixNetworkInput (ordinaryFit n) hpl 1 (Fin.cast hclen' x.1, x.2))).val := by
    intro x
    simpa only [prefixNetworkInput_cast] using hcplaced x
  have hpop := installed_prefix_population_exact (ordinaryFit n) (diagonalFit n)
    (fc2k_prefix_pair_allocation n) rectangleFit (squareFit hn) rectangleChoice
    (allocatorValues lower (by omega) hnmax) b
    (bridgeRepeatedPermutations 1 p) (bridgeRepeatedPermutations 1 p)
    hpl hpl rows cols hrlen' hclen' hrect hrplaced' hcplaced'
  have hcard := prefixPopulation_card (allocatorValues lower (by omega) hnmax)
    (allocatorValues_injective lower (by omega) hnmax)
  refine ⟨p, rows, cols, hrlen, hclen, b, hder, hexp, hrmap, hcmap, ?_, ?_,
    hdisjoint, hrect, hrplaced, hcplaced, ?_, ?_, hrgap, hcgap⟩
  · simpa [rectangleCells] using hrpack
  · simpa [rectangleCells] using hcpack
  · simpa [rectangleCells] using hpop
  · rw [show (rectangleCells hn ∪ (LayerPacking.layersSupport rows ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols))).image (entry b) =
      (Finset.univ : Finset ((Fin 1 × Fin (6 * (n + 8))) × Bool)).image
        (fun x => (allocatorValues lower (by omega) hnmax x).val) by
      simpa [rectangleCells] using hpop]
    simpa using hcard

end
end Sude.GeneratedPrefix.LStage0
