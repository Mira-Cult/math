import Sude.FWGrowthFullMidpointFromComponents
import Sude.FWGrowthOrdinaryCenteredReference
import Sude.FWGrowthOrdinaryRecenterLineBound

/-! Full growth-family midpoint discrepancy on the same supplied square.
Signed endpoint orientations and all other families remain separate. -/
namespace Sude
noncomputable section

/-- The ordinary DP/E3 estimate and actual rectangle geometry yield the full
growth midpoint estimate on every row and column, centered at original trace
stage means. All witnesses and midpoint-placement assumptions refer to the
same supplied square. -/
theorem fw_growth_full_midpoint_bound {n L : ℕ} (hn : 0 < n)
    {initial final : Finset ℕ} {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 (6*(n+8)) initial radius final last stages)
    (X : ℝ) (hX : 0 ≤ X) (hnarrow : NarrowedStages (X/6) stages)
    (ω₀ ω : Fin stages.length → Equiv.Perm (Fin (6*(n+8))))
    (T U V : Fin stages.length → Finset ℕ)
    (hmap : ∀ j, (fwGrowthMainSlots n).image (fun i => trace.lowAt rfl j (ω₀ j i)) = T j ∧
      (fwGrowthAntiSlots n).image (fun i => trace.lowAt rfl j (ω₀ j i)) = U j ∧
      (fwGrowthPartnerSlots n).image (fun i => trace.lowAt rfl j (ω₀ j i)) = V j)
    (hsel : ∀ j, T j ⊆ (stages.get j).lows ∧ U j ⊆ (stages.get j).lows \ T j ∧
      V j ⊆ (stages.get j).lows \ (T j ∪ U j) ∧
      (T j).card = 12 ∧ (U j).card = 12 ∧ (V j).card = 24)
    (hE : |(∑ j, ∑ p ∈ ((T j ∪ U j) ∪ V j), growthStageMidpoint (stages.get j) p) -
      (48 : ℝ) * ∑ j, ((∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) /
        (6*(n+8) : ℕ))| ≤ (3/2:ℝ)*(X/6))
    (offset : ℕ) (hoff : offset + stages.length*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = stages.length*3) (hc : cols.length = stages.length*3)
    (a : Cell n ≃ Fin (n*n))
    (hmid : ∀ (j : Fin stages.length) (rect : Fin (4*6)) (pair : Fin 2),
      let i := prefixDiagonalPairIndex (show (4*6)*2 ≤ 6*(n+8) by omega) (rect,pair)
      (((entry a (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
          offset hoff hs choice rows cols hr hc ((j,i),true)) : ℝ) +
        entry a (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
          offset hoff hs choice rows cols hr hc ((j,i),false))) / 2) =
        growthStageMidpoint (stages.get j) (trace.lowAt rfl j (ω j i)))
    (hbound :
      let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        offset hoff hs choice rows cols hr hc
      let pop := fwGrowthOrdinaryPopulation n stages.length
      let midpoint := fun s : Fin stages.length × Fin (6*(n+8)) =>
        growthStageMidpoint (stages.get s.1) (trace.lowAt rfl s.1 (ω₀ s.1 s.2))
      ∀ l : Fin ((n+n)+2),
        |(∑ s : {s // s ∈ pop}, physicalPairLineWeight cells
            (fun c => c ∈ physicalAllLineCells l) s.val *
            (((entry a (cells (s.val,true)) : ℝ) + entry a (cells (s.val,false))) / 2)) -
          ∑ j ∈ pop.image Prod.fst,
            (∑ s ∈ pop.filter (fun s => s.1 = j), physicalPairLineWeight cells
              (fun c => c ∈ physicalAllLineCells l) s) *
                prefixOriginalStageMean pop Prod.fst midpoint j| ≤
          (Nat.clog 2 (6*n) : ℝ) * (8 * (X/6))) :
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice rows cols hr hc
    let μ := fun j => (∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) /
      (6*(n+8) : ℕ)
    (∀ r : Fin n,
      |∑ s : Fin stages.length × Fin (6*(n+8)),
        physicalPairLineWeight cells (fun c => c.1 = r) s *
          ((((entry a (cells (s,true)) : ℝ) + entry a (cells (s,false))) / 2) - μ s.1)| ≤
        (Nat.clog 2 (6*n) : ℝ) * (8*(X/6)) + 3*(X/6)/(n : ℝ) + 2*(X/6)) ∧
    (∀ c : Fin n,
      |∑ s : Fin stages.length × Fin (6*(n+8)),
        physicalPairLineWeight cells (fun q => q.2 = c) s *
          ((((entry a (cells (s,true)) : ℝ) + entry a (cells (s,false))) / 2) - μ s.1)| ≤
        (Nat.clog 2 (6*n) : ℝ) * (8*(X/6)) + 3*(X/6)/(n : ℝ) + 2*(X/6)) := by
  classical
  dsimp only
  let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
    offset hoff hs choice rows cols hr hc
  let pop := fwGrowthOrdinaryPopulation n stages.length
  let μ : Fin stages.length → ℝ := fun j =>
    (∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) / (6*(n+8) : ℕ)
  let mid : Fin stages.length × Fin (6*(n+8)) → ℝ := fun s =>
    (((entry a (cells (s,true)) : ℝ) + entry a (cells (s,false))) / 2)
  let B : ℝ := (Nat.clog 2 (6*n) : ℝ) * (8*(X/6)) + 3*(X/6)/(n : ℝ)
  have hb := fw_growth_ordinary_recentered_rows_columns hn trace ω₀ T U V X hmap hsel hE
    offset hoff hs choice rows cols hr hc a hbound
  have hmass := fw_growth_ordinary_population_row_column_mass offset hoff hs choice rows cols hr hc
  have hordR : ∀ r : Fin n, |∑ s : {s // s ∈ pop},
      physicalPairLineWeight cells (fun c => c.1 = r) s.val * (mid s.val - μ s.val.1)| ≤ B := by
    intro r
    let line := fwGrowthRowLineLabel r
    have hl : line ∈ (Finset.univ.image fwGrowthRowLineLabel ∪ Finset.univ.image fwGrowthColumnLineLabel :
        Finset (Fin ((n+n)+2))) := Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩)
    have h := hb line hl
    have hmass' : ∀ j, (∑ s ∈ pop.filter (fun s => s.1 = j),
        physicalPairLineWeight cells (fun c => c.1 = r) s) = 12 := by
      intro j
      simpa only [cells, pop, fwGrowthRowLineLabel, physicalAllLineCells, Equiv.symm_apply_apply, mem_rowCells] using (hmass j).1 r
    have he := fw_growth_ordinary_centered_reference hn
      (fun s => physicalPairLineWeight cells (fun c => c.1 = r) s) mid μ hmass'
    rw [he]
    simpa only [line, cells, pop, μ, mid, B, fwGrowthRowLineLabel, physicalAllLineCells,
      Equiv.symm_apply_apply, mem_rowCells] using h
  have hordC : ∀ c : Fin n, |∑ s : {s // s ∈ pop},
      physicalPairLineWeight cells (fun q => q.2 = c) s.val * (mid s.val - μ s.val.1)| ≤ B := by
    intro c
    let line := fwGrowthColumnLineLabel c
    have hl : line ∈ (Finset.univ.image fwGrowthRowLineLabel ∪ Finset.univ.image fwGrowthColumnLineLabel :
        Finset (Fin ((n+n)+2))) := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩)
    have h := hb line hl
    have hmass' : ∀ j, (∑ s ∈ pop.filter (fun s => s.1 = j),
        physicalPairLineWeight cells (fun q => q.2 = c) s) = 12 := by
      intro j
      simpa only [cells, pop, fwGrowthColumnLineLabel, physicalAllLineCells, Equiv.symm_apply_apply, mem_columnCells] using (hmass j).2 c
    have he := fw_growth_ordinary_centered_reference hn
      (fun s => physicalPairLineWeight cells (fun q => q.2 = c) s) mid μ hmass'
    rw [he]
    simpa only [line, cells, pop, μ, mid, B, fwGrowthColumnLineLabel, physicalAllLineCells,
      Equiv.symm_apply_apply, mem_columnCells] using h
  exact fw_growth_full_midpoint_from_components trace X hX hnarrow ω offset hoff hs choice rows cols hr hc a hmid B hordR hordC

end
end Sude
