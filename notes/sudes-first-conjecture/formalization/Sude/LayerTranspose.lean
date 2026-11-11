import Sude.LayerSequence

/-! Transposition of actual placements and reserved cells, including both
labelled diagonals. -/
namespace Sude.LayerPacking
noncomputable section

def transposePlacement {n : ℕ} (a : Cell n ≃ Fin (n * n)) : Cell n ≃ Fin (n * n) :=
  (Equiv.prodComm (Fin n) (Fin n)).trans a

def transposeCells {n : ℕ} (s : Finset (Cell n)) : Finset (Cell n) := s.image Prod.swap

@[simp] theorem entry_transposePlacement {n : ℕ} (a : Cell n ≃ Fin (n * n)) (i j : Fin n) :
    entry (transposePlacement a) (i, j) = entry a (j, i) := rfl

@[simp] theorem transposePlacement_involutive {n : ℕ} (a : Cell n ≃ Fin (n * n)) :
    transposePlacement (transposePlacement a) = a := by
  ext ⟨i, j⟩
  rfl

@[simp] theorem transposeCells_involutive {n : ℕ} (s : Finset (Cell n)) :
    transposeCells (transposeCells s) = s := by
  ext ⟨i, j⟩
  simp [transposeCells]

@[simp] theorem rowSum_transpose {n : ℕ} (a : Cell n ≃ Fin (n * n)) (i : Fin n) :
    rowSum (transposePlacement a) i = columnSum a i := by
  simp [rowSum, columnSum]

@[simp] theorem columnSum_transpose {n : ℕ} (a : Cell n ≃ Fin (n * n)) (i : Fin n) :
    columnSum (transposePlacement a) i = rowSum a i := by
  simp [rowSum, columnSum]

@[simp] theorem mainSum_transpose {n : ℕ} (a : Cell n ≃ Fin (n * n)) :
    mainSum (transposePlacement a) = mainSum a := by
  simp [mainSum]

@[simp] theorem antiSum_transpose {n : ℕ} (a : Cell n ≃ Fin (n * n)) :
    antiSum (transposePlacement a) = antiSum a := by
  simp only [antiSum, entry_transposePlacement]
  have h := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin n))
    (fun i : Fin n => entry a (i, i.rev))
  simpa using h

@[simp] theorem rowUsed_transpose {n : ℕ} (s : Finset (Cell n)) (i : Fin n) :
    rowUsed (transposeCells s) i = colUsed s i := by
  ext j
  simp [rowUsed, colUsed, transposeCells, Prod.ext_iff]

@[simp] theorem colUsed_transpose {n : ℕ} (s : Finset (Cell n)) (i : Fin n) :
    colUsed (transposeCells s) i = rowUsed s i := by
  ext j
  simp [rowUsed, colUsed, transposeCells, Prod.ext_iff]

@[simp] theorem swap_mem_main {n : ℕ} (z : Cell n) :
    z.swap ∈ mainCells n ↔ z ∈ mainCells n := by
  rcases z with ⟨i, j⟩
  simp [eq_comm]

@[simp] theorem swap_mem_anti {n : ℕ} (z : Cell n) :
    z.swap ∈ antiCells n ↔ z ∈ antiCells n := by
  rcases z with ⟨i, j⟩
  simp only [mem_antiCells, Prod.swap_prod_mk]
  constructor <;> intro h <;> have hh := congrArg Fin.rev h <;> simpa using hh.symm

/-- Transposition exchanges exact row and column occupancy counts. -/
theorem transposeCells_row_card {n : ℕ} (s : Finset (Cell n)) (i : Fin n) :
    ((transposeCells s).filter (fun z => z.1 = i)).card =
      (s.filter (fun z => z.2 = i)).card := by
  have hset : (transposeCells s).filter (fun z => z.1 = i) =
      transposeCells (s.filter (fun z => z.2 = i)) := by
    ext ⟨r, c⟩
    simp [transposeCells, Prod.ext_iff, eq_comm]; aesop
  rw [hset, transposeCells, Finset.card_image_of_injective]
  intro x y h
  have hs := congrArg Prod.swap h
  simpa using hs

theorem transposeCells_column_card {n : ℕ} (s : Finset (Cell n)) (i : Fin n) :
    ((transposeCells s).filter (fun z => z.2 = i)).card =
      (s.filter (fun z => z.1 = i)).card := by
  have hset : (transposeCells s).filter (fun z => z.2 = i) =
      transposeCells (s.filter (fun z => z.1 = i)) := by
    ext ⟨r, c⟩
    simp [transposeCells, Prod.ext_iff, eq_comm]
  rw [hset, transposeCells, Finset.card_image_of_injective]
  intro x y h
  have hs := congrArg Prod.swap h
  simpa using hs

/-- Transposed packed supports still avoid the original reservations and
both original-coordinate diagonals. -/
theorem PackedLayers.transposed_support_safe {n : ℕ} {reserved : Finset (Cell n)}
    {layers : List (Layer n)} (h : PackedLayers (transposeCells reserved) layers) :
    ∀ z ∈ transposeCells (layersSupport layers),
      z ∉ reserved ∧ z ∉ mainCells n ∧ z ∉ antiCells n := by
  intro z hz
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hz
  have hoff := h.support_off_diagonals c hc
  have hnot : c ∉ transposeCells reserved := by
    intro hr
    exact Finset.disjoint_left.mp h.reserved_disjoint hr hc
  refine ⟨?_, ?_, ?_⟩
  · intro hr
    apply hnot
    exact Finset.mem_image.mpr ⟨c.swap, hr, by simp⟩
  · exact fun hs => hoff.1 ((swap_mem_main c).mp hs)
  · exact fun hs => hoff.2 ((swap_mem_anti c).mp hs)

/-- Transposed version for the column network. This places the same supplied
pool values in actual original-coordinate cells, preserves the reservation,
and tracks every gap and both axis occupancies. -/
theorem pack_and_install_column_layers {n L : ℕ}
    (πs : List (Equiv.Perm (Fin n))) (reserved : Finset (Cell n))
    (hderange : ∀ π ∈ πs, ∀ i, π i ≠ i)
    (hrow : ∀ i, (rowUsed reserved i).card ≤ L)
    (hcol : ∀ j, (colUsed reserved j).card ≤ L)
    (hn : 4 * (L + 2 * πs.length) + 8 < n)
    (a : Cell n ≃ Fin (n * n))
    (values : (Fin πs.length × (Fin n × Bool)) → pool n)
    (hvalues : Function.Injective values)
    (havoid : ∀ x c, c ∈ reserved → (values x).val ≠ entry a c)
    (gap : Fin πs.length → Fin n → ℕ)
    (hgap : ∀ i e, (values (i, (e, true))).val =
      (values (i, (e, false))).val + gap i e) :
    ∃ (layers : List (Layer n)) (hlen : layers.length = πs.length)
      (b : Cell n ≃ Fin (n * n)),
      layers.map Prod.fst = πs ∧ PackedLayers (transposeCells reserved) layers ∧
      (∀ i e, entry b ((layers.get i).2 e, (layers.get i).1 e) =
        entry b ((layers.get i).2 e, e) + gap (Fin.cast hlen i) e) ∧
      (∀ x, entry b (sequenceCell layers x).swap = (values (Fin.cast hlen x.1, x.2)).val) ∧
      (∀ c ∈ reserved, entry b c = entry a c) ∧
      (∀ z ∈ transposeCells (layersSupport layers),
        z ∉ reserved ∧ z ∉ mainCells n ∧ z ∉ antiCells n) ∧
      (∀ r, ((transposeCells (layersSupport layers)).filter (fun z => z.1 = r)).card = 2 * πs.length) ∧
      (∀ c, ((transposeCells (layersSupport layers)).filter (fun z => z.2 = c)).card = 2 * πs.length) := by
  have hrow' : ∀ i, (rowUsed (transposeCells reserved) i).card ≤ L := by
    intro i
    simpa using hcol i
  have hcol' : ∀ i, (colUsed (transposeCells reserved) i).card ≤ L := by
    intro i
    simpa using hrow i
  have havoid' : ∀ x c, c ∈ transposeCells reserved →
      (values x).val ≠ entry (transposePlacement a) c := by
    intro x c hc
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hc
    rcases z with ⟨i, j⟩
    simpa using havoid x (i, j) hz
  obtain ⟨layers, hlen, bt, hmap, hpacked, hphysical, hplaced, hfixed, hrows, hcols⟩ :=
    pack_and_install_finite_layers πs (transposeCells reserved) hderange hrow' hcol' hn
      (transposePlacement a) values hvalues havoid' gap hgap
  refine ⟨layers, hlen, transposePlacement bt, hmap, hpacked, ?_, ?_, ?_,
    hpacked.transposed_support_safe, ?_, ?_⟩
  · intro i e
    simpa using hphysical i e
  · intro x
    have hh := hplaced x
    cases hc : sequenceCell layers x with
    | mk i j =>
      simp only [hc] at hh ⊢
      simpa using hh
  · intro c hc
    have hc' : c.swap ∈ transposeCells reserved := Finset.mem_image.mpr ⟨c, hc, rfl⟩
    have hh := hfixed c.swap hc'
    rcases c with ⟨i, j⟩
    simpa using hh
  · intro r
    rw [transposeCells_row_card]
    exact hcols r
  · intro c
    rw [transposeCells_column_card]
    exact hrows c

end
end Sude.LayerPacking
