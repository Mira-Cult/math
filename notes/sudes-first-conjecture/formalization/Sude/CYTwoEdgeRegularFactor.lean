import Sude.DenseCentralCompletion
/-! CY center-edge trimming under explicit residual-degree hypotheses.
The full FW incidence classification and global exception budget are separate. -/
namespace Sude
noncomputable section

theorem cy_trim_row_degrees {n : ℕ} (E : Finset (Cell n)) (center i j : Fin n)
    (hi : i ≠ center)
    (he1 : (center,j) ∈ E) (he2 : (i,center) ∈ E) :
    let E' := E \ ({(center,j), (i,center)} : Finset (Cell n))
    (LayerPacking.rowUsed E' center).card + 1 = (LayerPacking.rowUsed E center).card ∧
    (LayerPacking.rowUsed E' i).card + 1 = (LayerPacking.rowUsed E i).card ∧
    ∀ r, r ≠ center → r ≠ i → LayerPacking.rowUsed E' r = LayerPacking.rowUsed E r := by
  classical
  dsimp only
  have hcenter : LayerPacking.rowUsed (E \ ({(center,j), (i,center)} : Finset (Cell n))) center =
      (LayerPacking.rowUsed E center).erase j := by
    ext c
    simp [LayerPacking.rowUsed, Ne.symm hi, and_comm]
  have hirow : LayerPacking.rowUsed (E \ ({(center,j), (i,center)} : Finset (Cell n))) i =
      (LayerPacking.rowUsed E i).erase center := by
    ext c
    simp [LayerPacking.rowUsed, hi, and_comm]
  have hcMem : j ∈ LayerPacking.rowUsed E center := by simpa [LayerPacking.rowUsed] using he1
  have hiMem : center ∈ LayerPacking.rowUsed E i := by simpa [LayerPacking.rowUsed] using he2
  constructor
  · rw [hcenter]; exact Finset.card_erase_add_one hcMem
  · constructor
    · rw [hirow]; exact Finset.card_erase_add_one hiMem
    · intro r hr hc
      ext c
      simp [LayerPacking.rowUsed, hr, hc]

theorem cy_trim_column_degrees {n : ℕ} (E : Finset (Cell n)) (center i j : Fin n)
    (hj : j ≠ center)
    (he1 : (center,j) ∈ E) (he2 : (i,center) ∈ E) :
    let E' := E \ ({(center,j), (i,center)} : Finset (Cell n))
    (LayerPacking.colUsed E' center).card + 1 = (LayerPacking.colUsed E center).card ∧
    (LayerPacking.colUsed E' j).card + 1 = (LayerPacking.colUsed E j).card ∧
    ∀ c, c ≠ center → c ≠ j → LayerPacking.colUsed E' c = LayerPacking.colUsed E c := by
  classical
  dsimp only
  have hcenter : LayerPacking.colUsed (E \ ({(center,j), (i,center)} : Finset (Cell n))) center =
      (LayerPacking.colUsed E center).erase i := by
    ext r
    simp [LayerPacking.colUsed, Ne.symm hj, and_comm]
  have hjcol : LayerPacking.colUsed (E \ ({(center,j), (i,center)} : Finset (Cell n))) j =
      (LayerPacking.colUsed E j).erase center := by
    ext r
    simp [LayerPacking.colUsed, hj, and_comm]
  have hcMem : i ∈ LayerPacking.colUsed E center := by simpa [LayerPacking.colUsed] using he2
  have hjMem : center ∈ LayerPacking.colUsed E j := by simpa [LayerPacking.colUsed] using he1
  constructor
  · rw [hcenter]; exact Finset.card_erase_add_one hcMem
  · constructor
    · rw [hjcol]; exact Finset.card_erase_add_one hjMem
    · intro c hc hj'
      ext r
      simp [LayerPacking.colUsed, hc, hj']


/-- CY's two-edge trim yields a factor in the original support; center and
endpoint degree hypotheses are explicit. No global exception count follows. -/
theorem cy_two_edge_regular_factor {n r : ℕ} (E : Finset (Cell n)) (center i j : Fin n)
    (hi : i ≠ center) (hj : j ≠ center)
    (he1 : (center,j) ∈ E) (he2 : (i,center) ∈ E)
    (hpos : 2 ≤ r) (hdense : 3*n ≤ 4*r)
    (hrowlo : ∀ x, r ≤ (LayerPacking.rowUsed E x).card)
    (hcollo : ∀ x, r ≤ (LayerPacking.colUsed E x).card)
    (hrowhi : ∀ x, (LayerPacking.rowUsed E x).card ≤ r+3)
    (hcolhi : ∀ x, (LayerPacking.colUsed E x).card ≤ r+3)
    (hrowother : ∀ x, x ≠ center → (LayerPacking.rowUsed E x).card ≤ r+2)
    (hcolother : ∀ x, x ≠ center → (LayerPacking.colUsed E x).card ≤ r+2)
    (hrowcenter : r+1 ≤ (LayerPacking.rowUsed E center).card)
    (hcolcenter : r+1 ≤ (LayerPacking.colUsed E center).card)
    (hrowend : r+1 ≤ (LayerPacking.rowUsed E i).card)
    (hcolend : r+1 ≤ (LayerPacking.colUsed E j).card) :
    ∃ F ⊆ E, CellFactorRegular F (r-1) ∧
      (∀ x, (rowCells x ∩ (E \ F)).card ≤ 4) ∧
      (∀ x, (columnCells x ∩ (E \ F)).card ≤ 4) ∧
      (E \ F).card + (r-1)*n = E.card := by
  classical
  let T : Finset (Cell n) := {(center,j), (i,center)}
  have hrt := cy_trim_row_degrees E center i j hi he1 he2
  have hct := cy_trim_column_degrees E center i j hj he1 he2
  change (LayerPacking.rowUsed (E \ T) center).card + 1 = _ ∧ _ at hrt
  change (LayerPacking.colUsed (E \ T) center).card + 1 = _ ∧ _ at hct
  have hrtEnd : (LayerPacking.rowUsed (E \ T) i).card + 1 = (LayerPacking.rowUsed E i).card := hrt.2.1
  have hctEnd : (LayerPacking.colUsed (E \ T) j).card + 1 = (LayerPacking.colUsed E j).card := hct.2.1
  have hr : ∀ x, r ≤ (LayerPacking.rowUsed (E \ T) x).card ∧
      (LayerPacking.rowUsed (E \ T) x).card ≤ r+2 := by
    intro x
    by_cases hc : x = center
    · subst x; have hu := hrowhi center; omega
    · by_cases he : x = i
      · subst x; have hu := hrowother i hi; omega
      · rw [hrt.2.2 x hc he]; exact ⟨hrowlo x, hrowother x hc⟩
  have hc : ∀ x, r ≤ (LayerPacking.colUsed (E \ T) x).card ∧
      (LayerPacking.colUsed (E \ T) x).card ≤ r+2 := by
    intro x
    by_cases hc : x = center
    · subst x; have hu := hcolhi center; omega
    · by_cases he : x = j
      · subst x; have hu := hcolother j hj; omega
      · rw [hct.2.2 x hc he]; exact ⟨hcollo x, hcolother x hc⟩
  obtain ⟨F, hF, hreg⟩ := dense_residual_regular_factor (r := r) (Δ := 2) (E \ T)
    (fun x => (hr x).1) (fun x => (hr x).2)
    (fun x => (hc x).1) (fun x => (hc x).2) hdense (by omega)
  have hFE : F ⊆ E := hF.trans Finset.sdiff_subset
  have hr' : ∀ x, (LayerPacking.rowUsed E x).card ≤ (r-1)+4 := by
    intro x; have hh := hrowhi x; omega
  have hc' : ∀ x, (LayerPacking.colUsed E x).card ≤ (r-1)+4 := by
    intro x; have hh := hcolhi x; omega
  obtain ⟨hR,hC⟩ := factor_exception_degrees (t := 4) E F hFE (by simpa using hreg) hr' hc'
  have hcardF : F.card = (r-1)*n := by
    have h := Finset.card_eq_sum_card_fiberwise (s := F) (t := Finset.univ)
      (f := fun z : Cell n => z.1) (by intro z hz; simp)
    calc
      F.card = ∑ x : Fin n, (rowCells x ∩ F).card := by
        convert h using 1
        apply Finset.sum_congr rfl
        intro x hx
        congr 1
        ext z
        simp [mem_rowCells, and_comm]
      _ = ∑ _x : Fin n, (r-1) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [factor_row_cells_card]
        simpa using hreg.1 x
      _ = (r-1)*n := by simp [Nat.mul_comm]
  have hsplit := Finset.card_sdiff_add_card_eq_card hFE
  exact ⟨F, hFE, by simpa using hreg, hR, hC, by simpa [hcardF] using hsplit⟩

theorem cy_choose_center_trim_edges {n : ℕ} (E : Finset (Cell n)) (center : Fin n)
    (badRows badCols : Finset (Fin n))
    (hcenter : (center,center) ∉ E)
    (hrow : badCols.card < (LayerPacking.rowUsed E center).card)
    (hcol : badRows.card < (LayerPacking.colUsed E center).card) :
    ∃ r c : Fin n, (center,c) ∈ E ∧ (r,center) ∈ E ∧
      r ∉ badRows ∧ c ∉ badCols ∧ r ≠ center ∧ c ≠ center ∧
      (center,c) ≠ (r,center) := by
  obtain ⟨c, hcE, hcBad⟩ := Finset.exists_mem_notMem_of_card_lt_card hrow
  obtain ⟨r, hrE, hrBad⟩ := Finset.exists_mem_notMem_of_card_lt_card hcol
  have hc : (center,c) ∈ E := by simpa [LayerPacking.rowUsed] using hcE
  have hr : (r,center) ∈ E := by simpa [LayerPacking.colUsed] using hrE
  have hrc : r ≠ center := by
    intro h
    subst r
    exact hcenter hr
  have hcc : c ≠ center := by
    intro h
    subst c
    exact hcenter hc
  refine ⟨r,c,hc,hr,hrBad,hcBad,hrc,hcc,?_⟩
  intro he
  exact hrc (congrArg Prod.fst he).symm

/-- Choose both trim edges outside supplied bad vertex sets and construct a
regular factor of the original support, with exact total complement count. -/
theorem cy_choose_trim_and_regular_factor {n r : ℕ} (E : Finset (Cell n)) (center : Fin n)
    (badRows badCols : Finset (Fin n))
    (hcenter : (center,center) ∉ E)
    (hbadcol : badCols.card < (LayerPacking.rowUsed E center).card)
    (hbadrow : badRows.card < (LayerPacking.colUsed E center).card)
    (hpos : 2 ≤ r) (hdense : 3*n ≤ 4*r)
    (hrowlo : ∀ x, r ≤ (LayerPacking.rowUsed E x).card)
    (hcollo : ∀ x, r ≤ (LayerPacking.colUsed E x).card)
    (hrowhi : ∀ x, (LayerPacking.rowUsed E x).card ≤ r+3)
    (hcolhi : ∀ x, (LayerPacking.colUsed E x).card ≤ r+3)
    (hrowother : ∀ x, x ≠ center → (LayerPacking.rowUsed E x).card ≤ r+2)
    (hcolother : ∀ x, x ≠ center → (LayerPacking.colUsed E x).card ≤ r+2)
    (hrowcenter : r+1 ≤ (LayerPacking.rowUsed E center).card)
    (hcolcenter : r+1 ≤ (LayerPacking.colUsed E center).card)
    (hgoodrow : ∀ x, x ∉ badRows → r+1 ≤ (LayerPacking.rowUsed E x).card)
    (hgoodcol : ∀ x, x ∉ badCols → r+1 ≤ (LayerPacking.colUsed E x).card) :
    ∃ F ⊆ E, CellFactorRegular F (r-1) ∧
      (∀ x, (rowCells x ∩ (E \ F)).card ≤ 4) ∧
      (∀ x, (columnCells x ∩ (E \ F)).card ≤ 4) ∧
      (E \ F).card + (r-1)*n = E.card := by
  obtain ⟨i,j,he1,he2,higood,hjgood,hi,hj,_⟩ :=
    cy_choose_center_trim_edges E center badRows badCols hcenter hbadcol hbadrow
  exact cy_two_edge_regular_factor E center i j hi hj he1 he2 hpos hdense
    hrowlo hcollo hrowhi hcolhi hrowother hcolother hrowcenter hcolcenter
    (hgoodrow i higood) (hgoodcol j hjgood)

end
end Sude
