import Sude.CYFullKeepoutQ4
import Sude.CYTwoEdgeRegularFactor
import Sude.BalancedResidualCompletion
import Sude.CentralConstruct
/-! CY center trimming and factor on the exact full packed keepout. -/
namespace Sude
noncomputable section

theorem cy_full_keepout_post_diagonal_load {L n : ℕ}
    (hs : 2*L+1 ≤ n) (hn : 0<n) (hodd : Odd n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) rows)
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows)) cols) :
    let ρ := 2*(rows.length + cols.length)
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport cols)
    let final := full ∪ unreservedDiagonalCells full
    (∀ i, ρ+1 ≤ (LayerPacking.rowUsed final i).card ∧
      (LayerPacking.rowUsed final i).card ≤ ρ+4 ∧
      (i ≠ centerIndex n hn → ρ+2 ≤ (LayerPacking.rowUsed final i).card)) ∧
    (∀ i, ρ+1 ≤ (LayerPacking.colUsed final i).card ∧
      (LayerPacking.colUsed final i).card ≤ ρ+4 ∧
      (i ≠ centerIndex n hn → ρ+2 ≤ (LayerPacking.colUsed final i).card)) := by
  classical
  dsimp only
  let rect := packedRectangleSupport hs choice
  let diag := mainCells n ∪ antiCells n
  let ρ := 2*(rows.length+cols.length)
  let full := rect ∪ LayerPacking.layersSupport rows ∪ LayerPacking.transposeCells (LayerPacking.layersSupport cols)
  let final := full ∪ unreservedDiagonalCells full
  have hb := cy_rectangle_diagonal_layers_load hs choice rows cols hrows hcols
  change (∀ i, (LayerPacking.rowUsed final i).card = (LayerPacking.rowUsed (rect ∪ diag) i).card + ρ) ∧
    (∀ i, (LayerPacking.colUsed final i).card = (LayerPacking.colUsed (rect ∪ diag) i).card + ρ) at hb
  constructor
  · intro i
    have hd := cy_diagonal_line_card hn hodd i
    change (LayerPacking.rowUsed diag i).card = _ at hd
    have hsub : LayerPacking.rowUsed diag i ⊆ LayerPacking.rowUsed (rect ∪ diag) i := by
      intro j hj
      simpa [LayerPacking.rowUsed] using Finset.mem_union_right rect (by simpa [LayerPacking.rowUsed] using hj)
    have hlo := Finset.card_le_card hsub
    have hr := packedRectangleSupport_row_load hs choice i
    change (LayerPacking.rowUsed rect i).card ≤ 2 at hr
    have hu := Finset.card_union_le (LayerPacking.rowUsed rect i) (LayerPacking.rowUsed diag i)
    rw [← LayerPacking.rowUsed_union] at hu
    have heq := hb.1 i
    change ρ+1 ≤ (LayerPacking.rowUsed final i).card ∧
      (LayerPacking.rowUsed final i).card ≤ ρ+4 ∧
      (i ≠ centerIndex n hn → ρ+2 ≤ (LayerPacking.rowUsed final i).card)
    have hdlo : 1 ≤ (LayerPacking.rowUsed diag i).card := by rw [hd]; split_ifs <;> omega
    have hdhi : (LayerPacking.rowUsed diag i).card ≤ 2 := by rw [hd]; split_ifs <;> omega
    refine ⟨by omega, by omega, ?_⟩
    intro hcenter
    have hd2 : (LayerPacking.rowUsed diag i).card = 2 := by rw [hd]; simp [hcenter]
    omega
  · intro i
    have hd := cy_diagonal_col_card hn hodd i
    change (LayerPacking.colUsed diag i).card = _ at hd
    have hsub : LayerPacking.colUsed diag i ⊆ LayerPacking.colUsed (rect ∪ diag) i := by
      intro j hj
      simpa [LayerPacking.colUsed] using Finset.mem_union_right rect (by simpa [LayerPacking.colUsed] using hj)
    have hlo := Finset.card_le_card hsub
    have hr := packedRectangleSupport_column_load hs choice i
    change (LayerPacking.colUsed rect i).card ≤ 2 at hr
    have hu := Finset.card_union_le (LayerPacking.colUsed rect i) (LayerPacking.colUsed diag i)
    rw [← LayerPacking.colUsed_union] at hu
    have heq := hb.2 i
    change ρ+1 ≤ (LayerPacking.colUsed final i).card ∧
      (LayerPacking.colUsed final i).card ≤ ρ+4 ∧
      (i ≠ centerIndex n hn → ρ+2 ≤ (LayerPacking.colUsed final i).card)
    have hdlo : 1 ≤ (LayerPacking.colUsed diag i).card := by rw [hd]; split_ifs <;> omega
    have hdhi : (LayerPacking.colUsed diag i).card ≤ 2 := by rw [hd]; split_ifs <;> omega
    refine ⟨by omega, by omega, ?_⟩
    intro hcenter
    have hd2 : (LayerPacking.colUsed diag i).card = 2 := by rw [hd]; simp [hcenter]
    omega

theorem cy_full_keepout_regular_factor {L n : ℕ}
    (hs : 2*L+1 ≤ n) (hL : 3 ≤ L) (hn : 7 ≤ n) (hodd : Odd n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) rows)
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows)) cols)
    (hload : 4 * (2 * (rows.length + cols.length) + 4) ≤ n) :
    let ρ := 2*(rows.length+cols.length)
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport cols)
    let final := full ∪ unreservedDiagonalCells full
    let E := (Finset.univ : Finset (Cell n)) \ final
    ∃ F ⊆ E, CellFactorRegular F (n-ρ-5) ∧
      (∀ x, (rowCells x ∩ (E \ F)).card ≤ 4) ∧
      (∀ x, (columnCells x ∩ (E \ F)).card ≤ 4) ∧
      (E \ F).card + (n-ρ-5)*n = E.card := by
  classical
  dsimp only
  let ρ := 2*(rows.length+cols.length)
  let rect := packedRectangleSupport hs choice
  let diag := mainCells n ∪ antiCells n
  let full := rect ∪ LayerPacking.layersSupport rows ∪ LayerPacking.transposeCells (LayerPacking.layersSupport cols)
  let final := full ∪ unreservedDiagonalCells full
  let E := (Finset.univ : Finset (Cell n)) \ final
  let center := centerIndex n (by omega)
  let r := n-ρ-4
  let badRows := (Finset.univ : Finset (Fin n)).filter (fun x => (LayerPacking.rowUsed final x).card = ρ+4)
  let badCols := (Finset.univ : Finset (Fin n)).filter (fun x => (LayerPacking.colUsed final x).card = ρ+4)
  have hl : 4*(ρ+4) ≤ n := hload
  have hρ : ρ+4 ≤ n := by omega
  have hr : r+ρ+4 = n := by dsimp [r]; omega
  have hpos : 2 ≤ r := by omega
  have hdense : 3*n ≤ 4*r := by omega
  have hcardgap : L < r+3 := by omega
  have hfactor : r-1 = n-ρ-5 := by dsimp [r]; omega
  have hfull := cy_full_cy_q4_and_center hs hL (show 0<n by omega) hodd choice rows cols hrows hcols
  change badRows.card = L ∧ badCols.card = L ∧
    (LayerPacking.rowUsed final center).card = ρ+1 ∧
    (LayerPacking.colUsed final center).card = ρ+1 at hfull
  have hoccs := cy_full_keepout_post_diagonal_load hs (show 0<n by omega) hodd choice rows cols hrows hcols
  change (∀ x, ρ+1 ≤ (LayerPacking.rowUsed final x).card ∧
      (LayerPacking.rowUsed final x).card ≤ ρ+4 ∧
      (x ≠ center → ρ+2 ≤ (LayerPacking.rowUsed final x).card)) ∧
    (∀ x, ρ+1 ≤ (LayerPacking.colUsed final x).card ∧
      (LayerPacking.colUsed final x).card ≤ ρ+4 ∧
      (x ≠ center → ρ+2 ≤ (LayerPacking.colUsed final x).card)) at hoccs
  have hrowocc := hoccs.1
  have hcolocc := hoccs.2
  have hroweq : ∀ x, (LayerPacking.rowUsed E x).card + (LayerPacking.rowUsed final x).card = n := by
    intro x
    change (LayerPacking.rowUsed (Finset.univ \ final) x).card + _ = n
    rw [rowUsed_complement]
    simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (LayerPacking.rowUsed final x))
  have hcoleq : ∀ x, (LayerPacking.colUsed E x).card + (LayerPacking.colUsed final x).card = n := by
    intro x
    change (LayerPacking.colUsed (Finset.univ \ final) x).card + _ = n
    rw [colUsed_complement]
    simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (LayerPacking.colUsed final x))
  have hcenter : (center,center) ∉ E := by
    have hin : (center,center) ∈ final := (postDiagonal_contains_both full).1 ((mem_mainCells _).2 rfl)
    simp [E, hin]
  have hbadcol : badCols.card < (LayerPacking.rowUsed E center).card := by
    rw [hfull.2.1]
    have he := hroweq center
    omega
  have hbadrow : badRows.card < (LayerPacking.colUsed E center).card := by
    rw [hfull.1]
    have he := hcoleq center
    omega
  have hrowlo : ∀ x, r ≤ (LayerPacking.rowUsed E x).card := by
    intro x; have h := hrowocc x; have he := hroweq x; omega
  have hcollo : ∀ x, r ≤ (LayerPacking.colUsed E x).card := by
    intro x; have h := hcolocc x; have he := hcoleq x; omega
  have hrowhi : ∀ x, (LayerPacking.rowUsed E x).card ≤ r+3 := by
    intro x; have h := hrowocc x; have he := hroweq x; omega
  have hcolhi : ∀ x, (LayerPacking.colUsed E x).card ≤ r+3 := by
    intro x; have h := hcolocc x; have he := hcoleq x; omega
  have hrowother : ∀ x, x ≠ center → (LayerPacking.rowUsed E x).card ≤ r+2 := by
    intro x hx; have h := (hrowocc x).2.2 hx; have he := hroweq x; omega
  have hcolother : ∀ x, x ≠ center → (LayerPacking.colUsed E x).card ≤ r+2 := by
    intro x hx; have h := (hcolocc x).2.2 hx; have he := hcoleq x; omega
  have hrowcenter : r+1 ≤ (LayerPacking.rowUsed E center).card := by
    have h := hfull.2.2.1; have he := hroweq center; omega
  have hcolcenter : r+1 ≤ (LayerPacking.colUsed E center).card := by
    have h := hfull.2.2.2; have he := hcoleq center; omega
  have hgoodrow : ∀ x, x ∉ badRows → r+1 ≤ (LayerPacking.rowUsed E x).card := by
    intro x hx
    have hnq : (LayerPacking.rowUsed final x).card ≠ ρ+4 := by simpa [badRows] using hx
    have h := (hrowocc x).2.1; have he := hroweq x; omega
  have hgoodcol : ∀ x, x ∉ badCols → r+1 ≤ (LayerPacking.colUsed E x).card := by
    intro x hx
    have hnq : (LayerPacking.colUsed final x).card ≠ ρ+4 := by simpa [badCols] using hx
    have h := (hcolocc x).2.1; have he := hcoleq x; omega
  obtain ⟨F,hFE,hreg,hrow,hcol,hcard⟩ := cy_choose_trim_and_regular_factor E center badRows badCols
    hcenter hbadcol hbadrow hpos hdense hrowlo hcollo hrowhi hcolhi hrowother hcolother
    hrowcenter hcolcenter hgoodrow hgoodcol
  rw [hfactor] at hreg hcard
  exact ⟨F,hFE,hreg,hrow,hcol,hcard⟩
end
end Sude
