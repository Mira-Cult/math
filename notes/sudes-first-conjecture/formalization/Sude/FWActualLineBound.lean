import Sude.FWAllLineMidpoint
import Sude.PrefixActualDeviation

/-! Compose FW's selected-seed witness with its actual selected-line bound. -/
namespace Sude
noncomputable section

/-- FW's intermediate witness satisfies the actual selected-cell line bound.
The finite population, physical resources, residual completion, prime targets,
and the route as a whole remain explicit or open. -/
theorem fw_selected_actual_line_allocation (lower : RSIndexLower) (n : ℕ)
    (seeds bridges : Finset ℕ) (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hprime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hbridge : ∀ p ∈ bridges, poolMaximum n ≤ 4 * p)
    (hcount : 3650551 ≤ seeds.card)
    (otherChoice : Fin 384 → Bool)
    (rowPerms colPerms : List (Equiv.Perm (Fin n)))
    (hrlen : rowPerms.length = 16 * 3) (hclen : colPerms.length = 16 * 3)
    (hrderange : ∀ π ∈ rowPerms, ∀ i, π i ≠ i)
    (hcderange : ∀ π ∈ colPerms, ∀ i, π i ≠ i)
    (base : Finset (Cell n)) (Bload : ℕ)
    (hrload : ∀ i, (LayerPacking.rowUsed base i).card ≤ Bload)
    (hcload : ∀ i, (LayerPacking.colUsed base i).card ≤ Bload)
    (hcapacity : 4 * ((Bload + 2) + 2 * rowPerms.length + 2 * colPerms.length) + 8 < n)
    (a : Cell n ≃ Fin (n * n)) (hbase : ∀ c ∈ base, entry a c ∈ bridges)
    (hfree : ∀ x : Fin (16 * (4 * 6)) × Fin 4,
      packedRectangleCorner (by omega : 2 * 384 + 1 ≤ n)
        (bridgeDiagonalChoice (by decide : 16 * (4 * 6) ≤ 384) otherChoice)
        (Fin.castLE (by decide : 16 * (4 * 6) ≤ 384) x.1, x.2) ∉ base) :
    let Q := 6 * (n + 8)
    ∃ (candidates : Finset ℕ) (hcard : candidates.card = (16 + 2 - 1) * Q)
      (kept : Finset ℕ) (hsub : kept ⊆ Finset.range (16 + 2 - 1)) (hkept : kept.card = 16)
      (hinj : Function.Injective (sortedSeedEndpoint candidates (16 + 2 - 1) Q 2 hcard))
      (hav : ∀ x, sortedSeedEndpoint candidates (16 + 2 - 1) Q 2 hcard x ∈ poolFinset n \ bridges),
      candidates ⊆ seeds ∧
      ∃ (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = rowPerms.length)
        (hcols : cols.length = colPerms.length) (ω : Fin 16 → Equiv.Perm (Fin Q))
        (b : Cell n ≃ Fin (n * n)),
        rows.map Prod.fst = rowPerms ∧ cols.map Prod.fst = colPerms ∧
        LayerPacking.PackedLayers (base ∪ allocatedBridgeRectangleSupport
          (by decide : 16 * (4 * 6) ≤ 384) (by omega : 2 * 384 + 1 ≤ n)
          (bridgeDiagonalChoice (by decide : 16 * (4 * 6) ≤ 384) otherChoice)) rows ∧
        LayerPacking.PackedLayers (LayerPacking.transposeCells
          ((base ∪ allocatedBridgeRectangleSupport (by decide : 16 * (4 * 6) ≤ 384)
            (by omega : 2 * 384 + 1 ≤ n)
            (bridgeDiagonalChoice (by decide : 16 * (4 * 6) ≤ 384) otherChoice)) ∪
            LayerPacking.layersSupport rows)) cols ∧
        (∀ l, |stageLineCentered
          (physicalAllLineSlots (by omega : (4 * 6) * 2 + 2 * (3 * n) ≤ Q)
            (by omega : (4 * 6) * 2 ≤ Q))
          (physicalAllLineWeights (by omega : (4 * 6) * 2 + 2 * (3 * n) ≤ Q)
            (by omega : (4 * 6) * 2 ≤ Q) (by decide : 16 * (4 * 6) ≤ 384)
            (by omega : 2 * 384 + 1 ≤ n) otherChoice rows cols (hrows.trans hrlen) (hcols.trans hclen))
          (retainedStageMidpoint candidates (16 + 2 - 1) 16 Q 2 hcard kept hsub hkept) l ω| ≤
          Real.sqrt (((11 / 2 : ℝ) * ((2 ^ 30 : ℕ) : ℝ) ^ 2) *
            Real.log (4 * (((n + n) + 2 : ℕ) : ℝ)) / 2)) ∧
        (let cells := prefixPairCells
            (by omega : (4 * 6) * 2 + 2 * (3 * n) ≤ Q)
            (by omega : (4 * 6) * 2 ≤ Q)
            (by omega : (4 * 6) * 2 + 2 * (3 * n) = Q)
            (by decide : 16 * (4 * 6) ≤ 384) (by omega : 2 * 384 + 1 ≤ n)
            (bridgeDiagonalChoice (by decide : 16 * (4 * 6) ≤ 384) otherChoice)
            rows cols (hrows.trans hrlen) (hcols.trans hclen)
          let weights := physicalAllLineWeights
            (by omega : (4 * 6) * 2 + 2 * (3 * n) ≤ Q) (by omega : (4 * 6) * 2 ≤ Q)
            (by decide : 16 * (4 * 6) ≤ 384) (by omega : 2 * 384 + 1 ≤ n)
            otherChoice rows cols (hrows.trans hrlen) (hcols.trans hclen)
          let values := retainedStageMidpoint candidates (16 + 2 - 1) 16 Q 2 hcard kept hsub hkept
          ∀ l, |(∑ c ∈ (Finset.univ.image cells).filter (fun c => c ∈ physicalAllLineCells l), (entry b c : ℝ)) -
            (∑ j, ((∑ q, weights l j q) * ((∑ q, values j q) / (Q : ℝ)))) -
            (∑ p, physicalPairLineOrientation cells (fun c => c ∈ physicalAllLineCells l) p * ((2 : ℝ) / 2))| ≤
            Real.sqrt (((11 / 2 : ℝ) * ((2 ^ 30 : ℕ) : ℝ) ^ 2) *
              Real.log (4 * (((n + n) + 2 : ℕ) : ℝ)) / 2)) ∧
        (∀ x, entry b (prefixPhysicalCells (by decide : 16 * (4 * 6) ≤ 384)
          (by omega : 2 * 384 + 1 ≤ n) (bridgeDiagonalChoice (by decide : 16 * (4 * 6) ≤ 384) otherChoice)
          rows cols (hrows.trans hrlen) (hcols.trans hclen) x) =
          (permutedRetainedSeedValues candidates (16 + 2 - 1) 16 Q 2 hcard kept hsub hkept bridges hav ω
            (prefixPhysicalInput (by omega : (4 * 6) * 2 + 2 * (3 * n) ≤ Q)
              (by omega : (4 * 6) * 2 ≤ Q) x)).val) ∧
        (∀ c ∈ base, entry b c = entry a c) ∧
        Finset.univ.image (fun x => entry b (prefixPhysicalCells (by decide : 16 * (4 * 6) ≤ 384)
          (by omega : 2 * 384 + 1 ≤ n) (bridgeDiagonalChoice (by decide : 16 * (4 * 6) ≤ 384) otherChoice)
          rows cols (hrows.trans hrlen) (hcols.trans hclen) x)) =
            retainedSeedEndpoints candidates (16 + 2 - 1) Q 2 hcard kept hsub := by
  dsimp only
  let Q := 6 * (n + 8)
  have hQ : 0 < Q := by dsimp [Q]; omega
  have hfit : (4 * 6) * 2 + 2 * (3 * n) ≤ Q := by dsimp [Q]; omega
  have hdiag : (4 * 6) * 2 ≤ Q := by dsimp [Q]; omega
  have hexact : (4 * 6) * 2 + 2 * (3 * n) = Q := by dsimp [Q]; omega
  have hs : 2 * 384 + 1 ≤ n := by omega
  have hrect : 16 * (4 * 6) ≤ 384 := by decide
  obtain ⟨candidates, hcard, kept, hsub, hkept, hinj, hav, hsubset,
      rows, cols, hrows, hcols, ω, b, hrmap, hcmap, hrpack, hcpack,
      hbound, hplaced, hfixed, hused⟩ :=
    fw_selected_all_line_midpoint_allocation lower n seeds bridges hnlo hnhi hseed hprime hbridge hcount
      otherChoice rowPerms colPerms hrlen hclen hrderange hcderange base Bload hrload hcload hcapacity a hbase hfree
  have hdev := prefix_actual_line_deviation_le candidates hcard kept hsub hkept bridges hav hinj
    hQ hfit hdiag hexact hrect hs otherChoice rows cols (hrows.trans hrlen) (hcols.trans hclen)
    _ _ hrpack hcpack ω b hplaced
    (Real.sqrt (((11 / 2 : ℝ) * ((2 ^ 30 : ℕ) : ℝ) ^ 2) *
      Real.log (4 * (((n + n) + 2 : ℕ) : ℝ)) / 2)) hbound
  exact ⟨candidates, hcard, kept, hsub, hkept, hinj, hav, hsubset, rows, cols, hrows, hcols, ω, b,
    hrmap, hcmap, hrpack, hcpack, hbound, hdev, hplaced, hfixed, hused⟩

end
end Sude
