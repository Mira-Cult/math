import Sude.Switches

/-! Ordinary pair switches used by the row and column reservoirs. -/
namespace Sude
noncomputable section

/-- A physical swap is its own inverse, including coincident endpoints. -/
theorem swapPlacement_involutive {n : ℕ} (a : Cell n ≃ Fin (n * n)) (x y : Cell n) :
    swapPlacement (swapPlacement a x y) x y = a := by
  ext t
  simp [swapPlacement]

/-- A physical swap affects no entry outside its two actual cells. -/
theorem swapPlacement_outside {n : ℕ} (a : Cell n ≃ Fin (n * n)) (x y t : Cell n)
    (hx : t ≠ x) (hy : t ≠ y) : entry (swapPlacement a x y) t = entry a t := by
  rw [entry_swapPlacement, Equiv.swap_apply_of_ne_of_ne hx hy]

/-- Any labelled line avoiding the two cells is preserved exactly. -/
theorem swapPlacement_line_unchanged {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (s : Finset (Cell n)) (x y : Cell n) (hne : x ≠ y)
    (hx : x ∉ s) (hy : y ∉ s) :
    placementLineSum (swapPlacement a x y) s = placementLineSum a s := by
  have h := placementLineSum_swap_effect a s x y hne
  simp [hx, hy] at h
  omega

/-- A switch in one column transfers precisely the entry difference between
    its endpoint rows, with every other row unchanged. -/
theorem verticalSwap_row_effect {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (i j k r : Fin n) (hij : i ≠ j) :
    (rowSum (swapPlacement a (i, k) (j, k)) r : ℤ) - (rowSum a r : ℤ) =
      (if i = r then (entry a (j, k) : ℤ) - entry a (i, k) else 0) +
      (if j = r then (entry a (i, k) : ℤ) - entry a (j, k) else 0) := by
  have hne : (i, k) ≠ (j, k) := by
    intro h
    exact hij (congrArg Prod.fst h)
  have h := placementLineSum_swap_effect a (rowCells r) (i, k) (j, k) hne
  rw [placementLineSum_row, placementLineSum_row] at h
  simpa only [mem_rowCells] using h

/-- Swapping within one column preserves every column sum. -/
theorem verticalSwap_columns {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (i j k : Fin n) (hij : i ≠ j) :
    ∀ r, columnSum (swapPlacement a (i, k) (j, k)) r = columnSum a r := by
  have hne : (i, k) ≠ (j, k) := by
    intro h
    exact hij (congrArg Prod.fst h)
  intro r
  have h := placementLineSum_swap_effect a (columnCells r) (i, k) (j, k) hne
  rw [placementLineSum_column, placementLineSum_column] at h
  simp only [mem_columnCells] at h
  split_ifs at h <;> omega

/-- A switch in one row transfers precisely the entry difference between
    its endpoint columns, with every other column unchanged. -/
theorem horizontalSwap_column_effect {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (i j k r : Fin n) (hjk : j ≠ k) :
    (columnSum (swapPlacement a (i, j) (i, k)) r : ℤ) - (columnSum a r : ℤ) =
      (if j = r then (entry a (i, k) : ℤ) - entry a (i, j) else 0) +
      (if k = r then (entry a (i, j) : ℤ) - entry a (i, k) else 0) := by
  have hne : (i, j) ≠ (i, k) := by
    intro h
    exact hjk (congrArg Prod.snd h)
  have h := placementLineSum_swap_effect a (columnCells r) (i, j) (i, k) hne
  rw [placementLineSum_column, placementLineSum_column] at h
  simpa only [mem_columnCells] using h

/-- Swapping within one row preserves every row sum. -/
theorem horizontalSwap_rows {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (i j k : Fin n) (hjk : j ≠ k) :
    ∀ r, rowSum (swapPlacement a (i, j) (i, k)) r = rowSum a r := by
  have hne : (i, j) ≠ (i, k) := by
    intro h
    exact hjk (congrArg Prod.snd h)
  intro r
  have h := placementLineSum_swap_effect a (rowCells r) (i, j) (i, k) hne
  rw [placementLineSum_row, placementLineSum_row] at h
  simp only [mem_rowCells] at h
  split_ifs at h <;> omega

/-- A pair switch avoiding both labelled diagonals preserves both full sums;
    the shared center is therefore never silently omitted. -/
theorem swapPlacement_diagonals_unchanged {n : ℕ}
    (a : Cell n ≃ Fin (n * n)) (x y : Cell n) (hne : x ≠ y)
    (xm : x ∉ mainCells n) (ym : y ∉ mainCells n)
    (xa : x ∉ antiCells n) (ya : y ∉ antiCells n) :
    mainSum (swapPlacement a x y) = mainSum a ∧
      antiSum (swapPlacement a x y) = antiSum a := by
  have hm := swapPlacement_line_unchanged a (mainCells n) x y hne xm ym
  have ha := swapPlacement_line_unchanged a (antiCells n) x y hne xa ya
  rw [placementLineSum_main, placementLineSum_main] at hm
  rw [placementLineSum_anti, placementLineSum_anti] at ha
  exact ⟨by exact_mod_cast hm, by exact_mod_cast ha⟩

/-- If the central cell is deliberately switched with a cell outside both
    diagonals, the same actual change occurs in both labelled sums. -/
theorem centerSwap_changes_both_diagonals {n : ℕ}
    (a : Cell n ≃ Fin (n * n)) (hn : 0 < n) (hodd : Odd n) (y : Cell n)
    (ym : y ∉ mainCells n) (ya : y ∉ antiCells n) :
    let center := (centerIndex n hn, centerIndex n hn)
    (mainSum (swapPlacement a center y) : ℤ) - (mainSum a : ℤ) =
        (entry a y : ℤ) - entry a center ∧
    (antiSum (swapPlacement a center y) : ℤ) - (antiSum a : ℤ) =
        (entry a y : ℤ) - entry a center := by
  dsimp only
  have hc := centerCell_on_both_diagonals n hn hodd
  have hne : (centerIndex n hn, centerIndex n hn) ≠ y := by
    intro heq
    exact ym (heq ▸ hc.1)
  have hm := placementLineSum_swap_effect a (mainCells n)
    (centerIndex n hn, centerIndex n hn) y hne
  have ha := placementLineSum_swap_effect a (antiCells n)
    (centerIndex n hn, centerIndex n hn) y hne
  rw [placementLineSum_main, placementLineSum_main] at hm
  rw [placementLineSum_anti, placementLineSum_anti] at ha
  simp [hc.1, ym] at hm
  simp [hc.2, ya] at ha
  exact ⟨hm, ha⟩

end
end Sude
