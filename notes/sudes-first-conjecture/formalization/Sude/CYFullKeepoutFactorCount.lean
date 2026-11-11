import Sude.CYFullKeepoutFactor
import Sude.CYExactExceptionCount
import Sude.FWFullDiagonalOverlap
import Sude.FWFullReservationOccupancy

/-! CY13 for the actual full-capacity protected keepout. -/
namespace Sude
noncomputable section

theorem cy_full_prekeepout_card {L n : ℕ}
    (hs : 2*L+1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n))
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) rows)
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows)) cols) :
    (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport cols)).card =
        (2*(rows.length+cols.length))*n + 4*L := by
  classical
  have hdis : Disjoint (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows)
      (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    exact (hcols.transposed_support_safe z hz').1 hz
  have hccard : (LayerPacking.transposeCells (LayerPacking.layersSupport cols)).card =
      2 * n * cols.length := by
    unfold LayerPacking.transposeCells
    rw [Finset.card_image_of_injective _]
    · exact packed_layers_support_card hcols
    · intro a b hab
      have h := congrArg Prod.swap hab
      simpa using h
  rw [Finset.card_union_of_disjoint hdis, Finset.card_union_of_disjoint hrows.reserved_disjoint,
    packed_rectangle_full_card, packed_layers_support_card hrows, hccard]
  ring

/-- The complete protected keepout has exactly one diagonal corner per full
rectangle. Both ordinary layer families are off both diagonals. -/
theorem cy_full_keepout_diagonal_card {L n : ℕ} (hs : 2*L+1 ≤ n) (hL : 3 ≤ L)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) rows)
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows)) cols) :
    ((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∩
        (mainCells n ∪ antiCells n)).card = L := by
  classical
  have heq : (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∩
        (mainCells n ∪ antiCells n) =
      packedRectangleSupport hs choice ∩ (mainCells n ∪ antiCells n) := by
    ext z
    constructor
    · intro hz
      obtain ⟨hfull, hdiag⟩ := Finset.mem_inter.mp hz
      have hzrect : z ∈ packedRectangleSupport hs choice := by
        rcases Finset.mem_union.mp hfull with hR | hC
        · rcases Finset.mem_union.mp hR with hrect | hrow
          · exact hrect
          · have ho := hrows.support_off_diagonals z hrow
            rcases Finset.mem_union.mp hdiag with hm | ha
            · exact (ho.1 hm).elim
            · exact (ho.2 ha).elim
        · have ho := hcols.transposed_support_safe z hC
          rcases Finset.mem_union.mp hdiag with hm | ha
          · exact (ho.2.1 hm).elim
          · exact (ho.2.2 ha).elim
      exact Finset.mem_inter.mpr ⟨hzrect,hdiag⟩
    · intro hz
      obtain ⟨hrect,hdiag⟩ := Finset.mem_inter.mp hz
      exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_union_left _ hrect),hdiag⟩
  rw [heq]
  exact packed_rectangle_diagonal_exact hs hL choice


/-- The full physical keepout, including spare rectangles, has a CY factor
with at most 3n+1 exceptions, under the packed-layer and load hypotheses. -/
theorem cy_full_keepout_factor_and_total {L n : ℕ}
    (hs : 2*L+1 ≤ n) (hL : 3 ≤ L) (hn : 7 ≤ n) (hodd : Odd n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) rows)
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows)) cols)
    (hload : 4*(2*(rows.length+cols.length)+4) ≤ n) :
    let ρ := 2*(rows.length+cols.length)
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport cols)
    let final := full ∪ unreservedDiagonalCells full
    let E := (Finset.univ : Finset (Cell n)) \ final
    ∃ F ⊆ E, CellFactorRegular F (n-ρ-5) ∧
      (∀ x, (rowCells x ∩ (E \ F)).card ≤ 4) ∧
      (∀ x, (columnCells x ∩ (E \ F)).card ≤ 4) ∧
      (E \ F).card + 3*L = 3*n+1 ∧ (E \ F).card ≤ 3*n+1 := by
  classical
  dsimp only
  let ρ := 2*(rows.length+cols.length)
  let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport cols)
  let final := full ∪ unreservedDiagonalCells full
  let E := (Finset.univ : Finset (Cell n)) \ final
  have hF := cy_full_keepout_regular_factor hs hL hn hodd choice rows cols hrows hcols hload
  change ∃ F ⊆ E, CellFactorRegular F (n-ρ-5) ∧
      (∀ x, (rowCells x ∩ (E \ F)).card ≤ 4) ∧
      (∀ x, (columnCells x ∩ (E \ F)).card ≤ 4) ∧
      (E \ F).card + (n-ρ-5)*n = E.card at hF
  obtain ⟨F,hFE,hreg,hrow,hcol,hcard⟩ := hF
  have hfull : full.card = ρ*n + 4*L := cy_full_prekeepout_card hs choice rows cols hrows hcols
  have hinter : (full ∩ (mainCells n ∪ antiCells n)).card = L :=
    cy_full_keepout_diagonal_card hs hL choice rows cols hrows hcols
  have hfinal : final = full ∪ (mainCells n ∪ antiCells n) := by
    ext z
    simp only [final, unreservedDiagonalCells, Finset.mem_union, Finset.mem_sdiff]
    tauto
  have hsplit : (E \ F).card + (n-ρ-5)*n =
      ((Finset.univ : Finset (Cell n)) \ (full ∪ (mainCells n ∪ antiCells n))).card := by
    simpa [E, hfinal] using hcard
  have hk : (n-ρ-5)+ρ+5=n := by dsimp [ρ] at *; omega
  obtain ⟨htotal,hbound⟩ := cy_actual_exception_count full (by omega) hodd hfull hinter hsplit hk
  exact ⟨F,hFE,hreg,hrow,hcol,htotal,hbound⟩

end
end Sude
