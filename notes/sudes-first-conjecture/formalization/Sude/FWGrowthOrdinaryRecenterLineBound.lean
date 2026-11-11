import Sude.FWGrowthOrdinaryRecenter
import Sude.FWGrowthOrdinaryRowColumnMass
import Sude.FWGrowthDiagonalOrdinaryTraceDP

/-! Recenter physical ordinary-slot midpoint contributions on the original
trace-stage means. Diagonal and nonordinary line terms remain separate. -/
namespace Sude
noncomputable section

/-- Line labels for physical rows. -/
def fwGrowthRowLineLabel {n : ℕ} (r : Fin n) : Fin ((n+n)+2) :=
  finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inl r)))

/-- Line labels for physical columns. -/
def fwGrowthColumnLineLabel {n : ℕ} (c : Fin n) : Fin ((n+n)+2) :=
  finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inr c)))

/-- The actual ordinary pair incidence of each row and column is twelve per
stage. This is first-power weight mass, not the squared incidence invoice. -/
theorem fw_growth_ordinary_population_row_column_mass {n L P : ℕ}
    (offset : ℕ) (hoff : offset + P*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = P*3) (hc : cols.length = P*3) (j : Fin P) :
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice rows cols hr hc
    let pop := fwGrowthOrdinaryPopulation n P
    (∀ r : Fin n, (∑ s ∈ pop.filter (fun s => s.1 = j),
      physicalPairLineWeight cells (fun c => c ∈ physicalAllLineCells (fwGrowthRowLineLabel r)) s) = 12) ∧
    (∀ c : Fin n, (∑ s ∈ pop.filter (fun s => s.1 = j),
      physicalPairLineWeight cells (fun x => x ∈ physicalAllLineCells (fwGrowthColumnLineLabel c)) s) = 12) := by
  classical
  dsimp only
  let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
    offset hoff hs choice rows cols hr hc
  let pop := fwGrowthOrdinaryPopulation n P
  have hfiber : pop.filter (fun s => s.1 = j) = ({j} : Finset (Fin P)).product (fwGrowthOrdinarySlots n) := by
    ext ⟨k,i⟩
    simp [pop, fwGrowthOrdinaryPopulation, eq_comm, and_comm]
  constructor
  · intro r
    rw [hfiber, Finset.product_eq_sprod, Finset.sum_product, Finset.sum_singleton]
    simpa only [cells, fwGrowthRowLineLabel, physicalAllLineCells, Equiv.symm_apply_apply, mem_rowCells] using
      fw_growth_ordinary_row_mass offset hoff hs choice rows cols hr hc j r
  · intro c
    rw [hfiber, Finset.product_eq_sprod, Finset.sum_product, Finset.sum_singleton]
    simpa only [cells, fwGrowthColumnLineLabel, physicalAllLineCells, Equiv.symm_apply_apply, mem_columnCells] using
      fw_growth_ordinary_column_mass offset hoff hs choice rows cols hr hc j c


/-- The three selected families remove exactly 48 distinct stage labels. -/
theorem fw_growth_selected_union_facts {stages : List BTSelectedStage}
    (T U V : Fin stages.length → Finset ℕ)
    (hsel : ∀ j, T j ⊆ (stages.get j).lows ∧ U j ⊆ (stages.get j).lows \ T j ∧
      V j ⊆ (stages.get j).lows \ (T j ∪ U j) ∧
      (T j).card = 12 ∧ (U j).card = 12 ∧ (V j).card = 24) :
    (∀ j, ((T j ∪ U j) ∪ V j) ⊆ (stages.get j).lows) ∧
    (∀ j, ((T j ∪ U j) ∪ V j).card = 48) := by
  classical
  constructor
  · intro j p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · exact (hsel j).1 hp
      · exact (Finset.mem_sdiff.mp ((hsel j).2.1 hp)).1
    · exact (Finset.mem_sdiff.mp ((hsel j).2.2.1 hp)).1
  · intro j
    have htu : Disjoint (T j) (U j) := by
      apply Finset.disjoint_left.mpr
      intro p hp hq
      exact (Finset.mem_sdiff.mp ((hsel j).2.1 hq)).2 hp
    have huv : Disjoint (T j ∪ U j) (V j) := by
      apply Finset.disjoint_left.mpr
      intro p hp hq
      exact (Finset.mem_sdiff.mp ((hsel j).2.2.1 hq)).2 hp
    rw [Finset.card_union_of_disjoint huv, Finset.card_union_of_disjoint htu,
      (hsel j).2.2.2.1, (hsel j).2.2.2.2.1, (hsel j).2.2.2.2.2]

/-- Combine a same-square ordinary midpoint error with the aggregate E3
recentring. The weight mass must be twelve in each stage; the physical row
and column instances are proved separately above. -/
theorem fw_growth_ordinary_line_recentered {n : ℕ} (hn : 0 < n)
    {initial final : Finset ℕ} {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 (6*(n+8)) initial radius final last stages)
    (ω : Fin stages.length → Equiv.Perm (Fin (6*(n+8))))
    (T U V : Fin stages.length → Finset ℕ) (C B : ℝ)
    (hmap : ∀ j, (fwGrowthMainSlots n).image (fun i => trace.lowAt rfl j (ω j i)) = T j ∧
      (fwGrowthAntiSlots n).image (fun i => trace.lowAt rfl j (ω j i)) = U j ∧
      (fwGrowthPartnerSlots n).image (fun i => trace.lowAt rfl j (ω j i)) = V j)
    (hsel : ∀ j, T j ⊆ (stages.get j).lows ∧ U j ⊆ (stages.get j).lows \ T j ∧
      V j ⊆ (stages.get j).lows \ (T j ∪ U j) ∧
      (T j).card = 12 ∧ (U j).card = 12 ∧ (V j).card = 24)
    (hE : |(∑ j, ∑ p ∈ ((T j ∪ U j) ∪ V j), growthStageMidpoint (stages.get j) p) -
      (48 : ℝ) * ∑ j, ((∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) /
        (6*(n+8) : ℕ))| ≤ (3/2:ℝ)*C)
    (w : (Fin stages.length × Fin (6*(n+8))) → ℝ)
    (v : {s // s ∈ fwGrowthOrdinaryPopulation n stages.length} → ℝ)
    (hmass : ∀ j, (∑ s ∈ (fwGrowthOrdinaryPopulation n stages.length).filter
      (fun s => s.1 = j), w s) = 12)
    (hbound : |(∑ s, w s.val * v s) -
      ∑ j ∈ (fwGrowthOrdinaryPopulation n stages.length).image Prod.fst,
        (∑ s ∈ (fwGrowthOrdinaryPopulation n stages.length).filter (fun s => s.1 = j), w s) *
          prefixOriginalStageMean (fwGrowthOrdinaryPopulation n stages.length) Prod.fst
            (fun s => growthStageMidpoint (stages.get s.1) (trace.lowAt rfl s.1 (ω s.1 s.2))) j| ≤ B) :
    |(∑ s, w s.val * v s) -
      12 * ∑ j, ((∑ p ∈ (stages.get j).lows, growthStageMidpoint (stages.get j) p) /
        (6*(n+8) : ℕ))| ≤ B + 3*C/(n : ℝ) := by
  classical
  obtain ⟨hsub, hcard⟩ := fw_growth_selected_union_facts T U V hsel
  have hrec := fw_growth_ordinary_dp_reference_recenter hn trace ω T U V C hmap hsub hcard hE w hmass
  exact (abs_sub_le _ _ _).trans (add_le_add hbound hrec)


/-- The same trace placement and selected rectangle labels give actual row
and column ordinary-midpoint bounds around the original stage means. This
requires the ordinary DP bound and E3 bound on that same witness; it does not
bound the rectangle contribution or a complete line. -/
theorem fw_growth_ordinary_recentered_rows_columns {n L : ℕ} (hn : 0 < n)
    {initial final : Finset ℕ} {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace 2 (6*(n+8)) initial radius final last stages)
    (ω₀ : Fin stages.length → Equiv.Perm (Fin (6*(n+8))))
    (T U V : Fin stages.length → Finset ℕ) (X : ℝ)
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
    (a' : Cell n ≃ Fin (n*n))
    (hbound :
      let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        offset hoff hs choice rows cols hr hc
      let pop := fwGrowthOrdinaryPopulation n stages.length
      let midpoint := fun s : Fin stages.length × Fin (6*(n+8)) =>
        growthStageMidpoint (stages.get s.1) (trace.lowAt rfl s.1 (ω₀ s.1 s.2))
      ∀ l : Fin ((n+n)+2),
        |(∑ s : {s // s ∈ pop}, physicalPairLineWeight cells
            (fun c => c ∈ physicalAllLineCells l) s.val *
            (((entry a' (cells (s.val,true)) : ℝ) + entry a' (cells (s.val,false))) / 2)) -
          ∑ j ∈ pop.image Prod.fst,
            (∑ s ∈ pop.filter (fun s => s.1 = j), physicalPairLineWeight cells
              (fun c => c ∈ physicalAllLineCells l) s) *
                prefixOriginalStageMean pop Prod.fst midpoint j| ≤
          (Nat.clog 2 (6*n) : ℝ) * (8 * (X/6))) :
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice rows cols hr hc
    let pop := fwGrowthOrdinaryPopulation n stages.length
    let originalMean := 12 * ∑ j, ((∑ p ∈ (stages.get j).lows,
      growthStageMidpoint (stages.get j) p) / (6*(n+8) : ℕ))
    ∀ l ∈ (Finset.univ.image fwGrowthRowLineLabel ∪ Finset.univ.image fwGrowthColumnLineLabel :
      Finset (Fin ((n+n)+2))),
      |(∑ s : {s // s ∈ pop}, physicalPairLineWeight cells
          (fun c => c ∈ physicalAllLineCells l) s.val *
          (((entry a' (cells (s.val,true)) : ℝ) + entry a' (cells (s.val,false))) / 2)) - originalMean| ≤
        (Nat.clog 2 (6*n) : ℝ) * (8 * (X/6)) + 3*(X/6)/(n : ℝ) := by
  classical
  dsimp only at hbound ⊢
  intro l hl
  have hmassall := fw_growth_ordinary_population_row_column_mass offset hoff hs choice rows cols hr hc
  have hmass : ∀ j, (∑ s ∈ (fwGrowthOrdinaryPopulation n stages.length).filter
      (fun s => s.1 = j), physicalPairLineWeight
        (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
          offset hoff hs choice rows cols hr hc) (fun c => c ∈ physicalAllLineCells l) s) = 12 := by
    intro j
    rcases Finset.mem_union.mp hl with hl | hl
    · obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hl
      exact (hmassall j).1 r
    · obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hl
      exact (hmassall j).2 c
  exact fw_growth_ordinary_line_recentered hn trace ω₀ T U V (X/6)
    ((Nat.clog 2 (6*n) : ℝ) * (8*(X/6))) hmap hsel hE
    (fun s => physicalPairLineWeight (btGrowingOffsetPairCells (Q := 6*(n+8))
      (by omega) (by omega) (by omega) offset hoff hs choice rows cols hr hc)
      (fun c => c ∈ physicalAllLineCells l) s)
    (fun s => ((entry a' (btGrowingOffsetPairCells (Q := 6*(n+8))
      (by omega) (by omega) (by omega) offset hoff hs choice rows cols hr hc (s.val,true)) : ℝ) +
      entry a' (btGrowingOffsetPairCells (Q := 6*(n+8))
      (by omega) (by omega) (by omega) offset hoff hs choice rows cols hr hc (s.val,false))) / 2)
    hmass (hbound l)



end
end Sude
