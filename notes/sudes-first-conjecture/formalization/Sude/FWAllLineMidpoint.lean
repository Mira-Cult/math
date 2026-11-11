import Sude.FWNarrowSeed
import Sude.ExistsRetainedAllLine

/-! Compose FW's actual selected seed supply with the physical midpoint allocation. -/
namespace Sude
noncomputable section

/-- FW's selected twin-prime groups admit a packed all-line midpoint
allocation whenever the explicit finite population and physical resource
hypotheses hold. This is an intermediate construction, not a tail theorem:
line targets, routing, completion, and the finite population remain open. -/
theorem fw_selected_all_line_midpoint_allocation (lower : RSIndexLower) (n : ℕ)
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
  obtain ⟨candidates, hcard, hsubset, kept, hsub, hkept, ⟨z, hz, hmax, hsource⟩, hinj, hav⟩ :=
    fw_actual_narrow_seed lower n seeds bridges hnlo hnhi hseed hprime hbridge hcount
  obtain ⟨rows, cols, hrows, hcols, ω, b, hrmap, hcmap, hrpack, hcpack, hdis,
      hbound, hplaced, hfixed, hused⟩ :=
    exists_retained_all_line_source_allocation candidates hcard kept hsub hkept bridges hav hinj
      hQ (by decide : 6 = 2 * 3) z hmax ((11 / 2 : ℝ) * ((2 ^ 30 : ℕ) : ℝ) ^ 2) hsource
      hfit hdiag hexact hrect hs (by decide : 3 ≤ 384) otherChoice rowPerms colPerms hrlen hclen
      hrderange hcderange base hrload hcload hcapacity a hbase hfree
  exact ⟨candidates, hcard, kept, hsub, hkept, hinj, hav, hsubset, rows, cols, hrows, hcols, ω, b,
    hrmap, hcmap, hrpack, hcpack, hbound, hplaced, hfixed, hused⟩

end
end Sude
