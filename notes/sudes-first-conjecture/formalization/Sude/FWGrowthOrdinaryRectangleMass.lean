import Sude.FWGrowthOrdinaryRowColumnMass

/-! Exact growth-stage ordinary incidence after deleting the physical
rectangle contribution. Rectangle membership hypotheses concern the same
physical endpoint map and are discharged by a packed-geometry adapter. -/
namespace Sude
noncomputable section

/-- If rectangle slots and ordinary slots partition actual pair endpoints,
subtracting rectangle-restricted line weight leaves the ordinary weight. -/
theorem physical_pair_weight_outside_rectangle {P n Q : ℕ}
    (cells : (Fin P × Fin Q) × Bool → Cell n) (ordinary : Finset (Fin Q))
    (rect : Finset (Cell n)) (j : Fin P)
    (hrect : ∀ i side, cells ((j,i),side) ∈ rect ↔ i ∉ ordinary)
    (line : Cell n → Prop) [DecidablePred line] (i : Fin Q) :
    physicalPairLineWeight cells line (j,i) -
      physicalPairLineWeight cells (fun z => line z ∧ z ∈ rect) (j,i) =
      if i ∈ ordinary then physicalPairLineWeight cells line (j,i) else 0 := by
  classical
  by_cases hi : i ∈ ordinary
  · have hf : cells ((j,i),false) ∉ rect := fun hm => (hrect i false).mp hm hi
    have ht : cells ((j,i),true) ∉ rect := fun hm => (hrect i true).mp hm hi
    simp [physicalPairLineWeight, hi, hf, ht]
  · have hf : cells ((j,i),false) ∈ rect := (hrect i false).mpr hi
    have ht : cells ((j,i),true) ∈ rect := (hrect i true).mpr hi
    simp [physicalPairLineWeight, hi, hf, ht]
    ring

/-- Every growth stage has twelve ordinary endpoints on every row and column;
the exact active-rectangle classification remains an explicit hypothesis. -/
theorem fw_growth_ordinary_rectangle_line_mass {P n L : ℕ}
    (offset : ℕ) (hoff : offset + P*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (sr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = P*3) (hsc : sc.length = P*3)
    (rect : Finset (Cell n))
    (hrect : ∀ j i side,
      btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
        offset hoff hs choice sr sc hsr hsc ((j,i),side) ∈ rect ↔ i ∉ fwGrowthOrdinarySlots n) :
    let cells := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      offset hoff hs choice sr sc hsr hsc
    (∀ j : Fin P, ∀ r : Fin n,
      (∑ i : Fin (6*(n+8)),
        (physicalPairLineWeight cells (fun z => z.1 = r) (j,i) -
          physicalPairLineWeight cells (fun z => z.1 = r ∧ z ∈ rect) (j,i))) = 12) ∧
    (∀ j : Fin P, ∀ c : Fin n,
      (∑ i : Fin (6*(n+8)),
        (physicalPairLineWeight cells (fun z => z.2 = c) (j,i) -
          physicalPairLineWeight cells (fun z => z.2 = c ∧ z ∈ rect) (j,i))) = 12) := by
  classical
  dsimp only
  constructor
  · intro j r
    simp_rw [physical_pair_weight_outside_rectangle _ _ _ j (hrect j) (fun z => z.1 = r)]
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    exact fw_growth_ordinary_row_mass offset hoff hs choice sr sc hsr hsc j r
  · intro j c
    simp_rw [physical_pair_weight_outside_rectangle _ _ _ j (hrect j) (fun z => z.2 = c)]
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    exact fw_growth_ordinary_column_mass offset hoff hs choice sr sc hsr hsc j c

end
end Sude
