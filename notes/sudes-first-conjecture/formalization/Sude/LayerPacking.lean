import Sude.PrimePairMatching
import Mathlib.Combinatorics.Hall.Finite

/-! The PB section 4 physical permutation-layer matching. No graph expansion,
prime supply, probabilistic balancing, or full controller is asserted. -/
namespace Sude.LayerPacking
noncomputable section

/-- If every left and right vertex forbids at most b opposite vertices and
2b<n, Hall's condition yields a bijective assignment of edges to columns. -/
theorem dense_allowed_matching {n b : ℕ} (allowed : Fin n → Fin n → Prop)
    [DecidableRel allowed] (hb : 2 * b < n)
    (hleft : ∀ i, ((Finset.univ : Finset (Fin n)).filter (fun j => ¬ allowed i j)).card ≤ b)
    (hright : ∀ j, ((Finset.univ : Finset (Fin n)).filter (fun i => ¬ allowed i j)).card ≤ b) :
    ∃ f : Fin n ≃ Fin n, ∀ i, allowed i (f i) := by
  classical
  let neighbors : Fin n → Finset (Fin n) := fun i => Finset.univ.filter (allowed i)
  have hall : ∀ S : Finset (Fin n), S.card ≤ (S.biUnion neighbors).card := by
    intro S
    by_cases hempty : S = ∅
    · simp [hempty]
    · have hnon : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
      by_cases hsmall : 2 * S.card ≤ n
      · obtain ⟨i, hi⟩ := hnon
        have hsub : neighbors i ⊆ S.biUnion neighbors := by
          intro j hj
          exact Finset.mem_biUnion.mpr ⟨i, hi, hj⟩
        have hcard := Finset.card_le_card hsub
        have hpartition := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (allowed i)
        have hbad := hleft i
        simp only [Finset.card_univ, Fintype.card_fin] at hpartition
        change (neighbors i).card + _ = n at hpartition
        omega
      · have hallcols : S.biUnion neighbors = Finset.univ := by
          apply Finset.eq_univ_of_forall
          intro j
          by_contra hj
          have hsubset : S ⊆ (Finset.univ : Finset (Fin n)).filter (fun i => ¬ allowed i j) := by
            intro i hi
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            intro ha
            exact hj (Finset.mem_biUnion.mpr ⟨i, hi, by simpa [neighbors] using ha⟩)
          have hcard := Finset.card_le_card hsubset
          have hbad := hright j
          omega
        rw [hallcols, Finset.card_univ, Fintype.card_fin]
        simpa using Finset.card_le_univ S
  obtain ⟨f, hf, hfmem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' neighbors).mp hall
  refine ⟨Equiv.ofBijective f ⟨hf, Finite.injective_iff_surjective.mp hf⟩, ?_⟩
  intro i
  change allowed i (f i)
  simpa [neighbors] using hfmem i

/-- Distinct occupied columns of a row and occupied rows of a column. -/
def rowUsed {n : ℕ} (reserved : Finset (Cell n)) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => (i, j) ∈ reserved)

def colUsed {n : ℕ} (reserved : Finset (Cell n)) (j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (i, j) ∈ reserved)

/-- All columns which would collide with reservations or either diagonal for
one edge from i to π(i). -/
def blockedColumns {n : ℕ} (π : Equiv.Perm (Fin n)) (reserved : Finset (Cell n))
    (i : Fin n) : Finset (Fin n) :=
  {i, i.rev, π i, (π i).rev} ∪ rowUsed reserved i ∪ rowUsed reserved (π i)

/-- All edge indices which can collide at one given physical column. -/
def blockedEdges {n : ℕ} (π : Equiv.Perm (Fin n)) (reserved : Finset (Cell n))
    (j : Fin n) : Finset (Fin n) :=
  {j, j.rev, π.symm j, π.symm j.rev} ∪ colUsed reserved j ∪
    (colUsed reserved j).image π.symm

theorem blockedColumns_card {n L : ℕ} (π : Equiv.Perm (Fin n))
    (reserved : Finset (Cell n)) (hrow : ∀ i, (rowUsed reserved i).card ≤ L)
    (i : Fin n) : (blockedColumns π reserved i).card ≤ 2 * L + 4 := by
  have h4 : ({i, i.rev, π i, (π i).rev} : Finset (Fin n)).card ≤ 4 := Finset.card_le_four
  have h1 := Finset.card_union_le ({i, i.rev, π i, (π i).rev} : Finset (Fin n)) (rowUsed reserved i)
  have h2 := Finset.card_union_le
    ({i, i.rev, π i, (π i).rev} ∪ rowUsed reserved i) (rowUsed reserved (π i))
  have hr1 := hrow i
  have hr2 := hrow (π i)
  dsimp [blockedColumns]
  omega

theorem blockedEdges_card {n L : ℕ} (π : Equiv.Perm (Fin n))
    (reserved : Finset (Cell n)) (hcol : ∀ j, (colUsed reserved j).card ≤ L)
    (j : Fin n) : (blockedEdges π reserved j).card ≤ 2 * L + 4 := by
  have h4 : ({j, j.rev, π.symm j, π.symm j.rev} : Finset (Fin n)).card ≤ 4 := Finset.card_le_four
  have h1 := Finset.card_union_le ({j, j.rev, π.symm j, π.symm j.rev} : Finset (Fin n)) (colUsed reserved j)
  have h2 := Finset.card_union_le
    ({j, j.rev, π.symm j, π.symm j.rev} ∪ colUsed reserved j) ((colUsed reserved j).image π.symm)
  have hi : ((colUsed reserved j).image π.symm).card ≤ (colUsed reserved j).card := Finset.card_image_le
  have hc := hcol j
  dsimp [blockedEdges]
  omega

/-- An edge/column collision belongs to the actual column's blocked edge set.
This accounts for both ends of the permutation edge and both diagonals. -/
theorem blockedColumns_transpose {n : ℕ} (π : Equiv.Perm (Fin n))
    (reserved : Finset (Cell n)) (i j : Fin n)
    (h : j ∈ blockedColumns π reserved i) : i ∈ blockedEdges π reserved j := by
  simp only [blockedColumns, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    rowUsed, Finset.mem_filter, Finset.mem_univ, true_and, or_assoc] at h
  simp only [blockedEdges, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, or_assoc]
  rcases h with h | h | h | h | h | h
  · left; exact h.symm
  · right; left
    have := congrArg Fin.rev h
    simpa using this.symm
  · right; right; left
    have := congrArg π.symm h
    simpa using this.symm
  · right; right; right; left
    have := congrArg (fun x => π.symm x.rev) h
    simpa using this.symm
  · right; right; right; right; left
    simpa [colUsed] using h
  · right; right; right; right; right
    apply Finset.mem_image.mpr
    refine ⟨π i, ?_, by simp⟩
    simpa [colUsed] using h

/-- PB's permutation-layer matching with the actual row/column load bound.
The returned permutation chooses one physical column per directed edge and
avoids every reserved cell and both full diagonals. -/
theorem physical_layer_matching {n L : ℕ} (π : Equiv.Perm (Fin n))
    (reserved : Finset (Cell n))
    (hrow : ∀ i, (rowUsed reserved i).card ≤ L)
    (hcol : ∀ j, (colUsed reserved j).card ≤ L) (hn : 4 * L + 8 < n) :
    ∃ f : Equiv.Perm (Fin n), ∀ i,
      (i, f i) ∉ reserved ∧ (π i, f i) ∉ reserved ∧
      (i, f i) ∉ mainCells n ∧ (i, f i) ∉ antiCells n ∧
      (π i, f i) ∉ mainCells n ∧ (π i, f i) ∉ antiCells n := by
  classical
  let allowed : Fin n → Fin n → Prop := fun i j => j ∉ blockedColumns π reserved i
  have hleft : ∀ i, ((Finset.univ : Finset (Fin n)).filter (fun j => ¬ allowed i j)).card ≤ 2 * L + 4 := by
    intro i
    apply (Finset.card_le_card ?_).trans (blockedColumns_card π reserved hrow i)
    intro j hj
    simpa [allowed] using (Finset.mem_filter.mp hj).2
  have hright : ∀ j, ((Finset.univ : Finset (Fin n)).filter (fun i => ¬ allowed i j)).card ≤ 2 * L + 4 := by
    intro j
    apply (Finset.card_le_card ?_).trans (blockedEdges_card π reserved hcol j)
    intro i hi
    apply blockedColumns_transpose π reserved i j
    simpa [allowed] using (Finset.mem_filter.mp hi).2
  obtain ⟨f, hf⟩ := dense_allowed_matching allowed (by omega) hleft hright
  refine ⟨f, ?_⟩
  intro i
  have h := hf i
  dsimp [allowed] at h
  have h1 : (i, f i) ∉ reserved := by
    intro hmem
    apply h
    simp [blockedColumns, rowUsed, hmem]
  have h2 : (π i, f i) ∉ reserved := by
    intro hmem
    apply h
    simp [blockedColumns, rowUsed, hmem]
  have h3 : (i, f i) ∉ mainCells n := by
    intro hmem
    have heq : i = f i := (mem_mainCells _).mp hmem
    apply h
    simp [blockedColumns, ← heq]
  have h4 : (i, f i) ∉ antiCells n := by
    intro hmem
    have heq : f i = i.rev := (mem_antiCells _).mp hmem
    apply h
    simp [blockedColumns, heq]
  have h5 : (π i, f i) ∉ mainCells n := by
    intro hmem
    have heq : π i = f i := (mem_mainCells _).mp hmem
    apply h
    simp [blockedColumns, ← heq]
  have h6 : (π i, f i) ∉ antiCells n := by
    intro hmem
    have heq : f i = (π i).rev := (mem_antiCells _).mp hmem
    apply h
    simp [blockedColumns, heq]
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- The two physical cells used by each directed permutation edge. -/
def layerCell {n : ℕ} (π f : Equiv.Perm (Fin n)) (x : Fin n × Bool) : Cell n :=
  if x.2 then (π x.1, f x.1) else (x.1, f x.1)

def layerCells {n : ℕ} (π f : Equiv.Perm (Fin n)) : Finset (Cell n) :=
  Finset.univ.image (layerCell π f)

theorem layerCell_injective {n : ℕ} (π f : Equiv.Perm (Fin n))
    (hderange : ∀ i, π i ≠ i) : Function.Injective (layerCell π f) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  have hs : f i = f j := by
    cases b <;> cases c <;>
      simpa only [layerCell, Bool.false_eq_true, ↓reduceIte, Prod.snd]
        using congrArg Prod.snd h
  have hij : i = j := f.injective hs
  subst j
  cases b <;> cases c <;> simp_all [layerCell, hderange i, Ne.symm (hderange i)]

theorem mem_layerCells {n : ℕ} (π f : Equiv.Perm (Fin n)) (z : Cell n) :
    z ∈ layerCells π f ↔ ∃ i, z = (i, f i) ∨ z = (π i, f i) := by
  constructor
  · intro hz
    obtain ⟨⟨i, b⟩, _, heq⟩ := Finset.mem_image.mp hz
    refine ⟨i, ?_⟩
    cases b <;> simp [layerCell] at heq
    · exact Or.inl heq.symm
    · exact Or.inr heq.symm
  · rintro ⟨i, hi | hi⟩
    · apply Finset.mem_image.mpr
      exact ⟨(i, false), Finset.mem_univ _, by simpa [layerCell] using hi.symm⟩
    · apply Finset.mem_image.mpr
      exact ⟨(i, true), Finset.mem_univ _, by simpa [layerCell] using hi.symm⟩

/-- The exact two cells contributed by the layer to a given row. -/
theorem layer_row_eq {n : ℕ} (π f : Equiv.Perm (Fin n)) (r : Fin n) :
    (layerCells π f).filter (fun z => z.1 = r) =
      {(r, f r), (r, f (π.symm r))} := by
  ext z
  simp only [Finset.mem_filter, mem_layerCells, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨i, hi | hi⟩, hrow⟩
    · subst z
      have : i = r := hrow
      subst i
      exact Or.inl rfl
    · subst z
      have hπ : π i = r := hrow
      have hi : i = π.symm r := by simpa using congrArg π.symm hπ
      subst i
      exact Or.inr (by simp)
  · rintro (hz | hz)
    · subst z
      exact ⟨⟨r, Or.inl rfl⟩, rfl⟩
    · subst z
      refine ⟨⟨π.symm r, Or.inr ?_⟩, rfl⟩
      simp

/-- The exact two cells contributed by the layer to a given column. -/
theorem layer_column_eq {n : ℕ} (π f : Equiv.Perm (Fin n)) (c : Fin n) :
    (layerCells π f).filter (fun z => z.2 = c) =
      {(f.symm c, c), (π (f.symm c), c)} := by
  ext z
  simp only [Finset.mem_filter, mem_layerCells, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨i, hi | hi⟩, hcol⟩
    · subst z
      have hi : i = f.symm c := by simpa using congrArg f.symm hcol
      subst i
      exact Or.inl (by simp)
    · subst z
      have hi : i = f.symm c := by simpa using congrArg f.symm hcol
      subst i
      exact Or.inr (by simp)
  · rintro (hz | hz)
    · subst z
      refine ⟨⟨f.symm c, Or.inl ?_⟩, rfl⟩
      simp
    · subst z
      refine ⟨⟨f.symm c, Or.inr ?_⟩, rfl⟩
      simp

/-- Each row and column receives exactly two distinct physical cells. -/
theorem layer_balanced {n : ℕ} (π f : Equiv.Perm (Fin n))
    (hderange : ∀ i, π i ≠ i) :
    (∀ r, ((layerCells π f).filter (fun z => z.1 = r)).card = 2) ∧
    (∀ c, ((layerCells π f).filter (fun z => z.2 = c)).card = 2) := by
  constructor
  · intro r
    rw [layer_row_eq]
    apply Finset.card_pair
    intro heq
    have hc : f r = f (π.symm r) := congrArg Prod.snd heq
    have hi : r = π.symm r := f.injective hc
    have hh : π r = r := by simpa using congrArg π hi
    exact hderange r hh
  · intro c
    rw [layer_column_eq]
    apply Finset.card_pair
    intro heq
    have hr : f.symm c = π (f.symm c) := congrArg Prod.fst heq
    exact hderange (f.symm c) hr.symm

/-- One layer uses exactly 2n distinct cells. -/
theorem layerCells_card {n : ℕ} (π f : Equiv.Perm (Fin n))
    (hderange : ∀ i, π i ≠ i) : (layerCells π f).card = 2 * n := by
  rw [layerCells, Finset.card_image_of_injective _ (layerCell_injective π f hderange)]
  simp [Fintype.card_prod, Nat.mul_comm]

/-- The source's full single-layer geometric conclusion, including both
physical avoidance and exact occupancy balance. -/
theorem physical_balanced_layer {n L : ℕ} (π : Equiv.Perm (Fin n))
    (hderange : ∀ i, π i ≠ i) (reserved : Finset (Cell n))
    (hrow : ∀ i, (rowUsed reserved i).card ≤ L)
    (hcol : ∀ j, (colUsed reserved j).card ≤ L) (hn : 4 * L + 8 < n) :
    ∃ f : Equiv.Perm (Fin n), Function.Injective (layerCell π f) ∧
      (∀ z ∈ layerCells π f, z ∉ reserved ∧ z ∉ mainCells n ∧ z ∉ antiCells n) ∧
      (layerCells π f).card = 2 * n ∧
      (∀ r, ((layerCells π f).filter (fun z => z.1 = r)).card = 2) ∧
      (∀ c, ((layerCells π f).filter (fun z => z.2 = c)).card = 2) := by
  obtain ⟨f, hf⟩ := physical_layer_matching π reserved hrow hcol hn
  refine ⟨f, layerCell_injective π f hderange, ?_, layerCells_card π f hderange,
    (layer_balanced π f hderange).1, (layer_balanced π f hderange).2⟩
  intro z hz
  obtain ⟨i, hi | hi⟩ := (mem_layerCells π f z).mp hz
  · subst z
    exact ⟨(hf i).1, (hf i).2.2.1, (hf i).2.2.2.1⟩
  · subst z
    exact ⟨(hf i).2.1, (hf i).2.2.2.2.1, (hf i).2.2.2.2.2⟩

/-- Supplied distinct pool entries with the desired gaps can be installed in
an actual balanced layer while every earlier reserved entry stays fixed. -/
theorem place_physical_balanced_layer {n L : ℕ}
    (a : Cell n ≃ Fin (n * n)) (π : Equiv.Perm (Fin n))
    (hderange : ∀ i, π i ≠ i) (reserved : Finset (Cell n))
    (hrow : ∀ i, (rowUsed reserved i).card ≤ L)
    (hcol : ∀ j, (colUsed reserved j).card ≤ L) (hn : 4 * L + 8 < n)
    (values : Fin n × Bool → pool n) (hvalues : Function.Injective values)
    (havoid : ∀ x c, c ∈ reserved → (values x).val ≠ entry a c)
    (gap : Fin n → ℕ)
    (hgap : ∀ i, (values (i, true)).val = (values (i, false)).val + gap i) :
    ∃ (f : Equiv.Perm (Fin n)) (b : Cell n ≃ Fin (n * n)),
      (∀ i, entry b (π i, f i) = entry b (i, f i) + gap i) ∧
      (∀ c ∈ reserved, entry b c = entry a c) ∧
      (∀ z ∈ layerCells π f, z ∉ reserved ∧ z ∉ mainCells n ∧ z ∉ antiCells n) ∧
      (layerCells π f).card = 2 * n ∧
      (∀ r, ((layerCells π f).filter (fun z => z.1 = r)).card = 2) ∧
      (∀ c, ((layerCells π f).filter (fun z => z.2 = c)).card = 2) := by
  obtain ⟨f, hinj, hsafe, hcard, hrows, hcols⟩ :=
    physical_balanced_layer π hderange reserved hrow hcol hn
  have hnew : ∀ x, layerCell π f x ∉ reserved := by
    intro x
    apply (hsafe (layerCell π f x) ?_).1
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  obtain ⟨b, hplace, hfixed⟩ :=
    place_distinct_pool_entries_preserving a (layerCell π f) values reserved hinj hvalues hnew havoid
  refine ⟨f, b, ?_, hfixed, hsafe, hcard, hrows, hcols⟩
  intro i
  have hlow := hplace (i, false)
  have hhigh := hplace (i, true)
  simp only [layerCell, Bool.false_eq_true, ↓reduceIte] at hlow hhigh
  rw [hhigh, hlow]
  exact hgap i

/-- The occupied-column set has exactly the same two entries as the row's
physical cells. -/
theorem rowUsed_layer_eq {n : ℕ} (π f : Equiv.Perm (Fin n)) (r : Fin n) :
    rowUsed (layerCells π f) r = {f r, f (π.symm r)} := by
  ext c
  have h := congrArg (fun s : Finset (Cell n) => (r, c) ∈ s) (layer_row_eq π f r)
  simpa [rowUsed] using h

/-- The occupied-row set has exactly the same two entries as the column's
physical cells. -/
theorem colUsed_layer_eq {n : ℕ} (π f : Equiv.Perm (Fin n)) (c : Fin n) :
    colUsed (layerCells π f) c = {f.symm c, π (f.symm c)} := by
  ext r
  have h := congrArg (fun s : Finset (Cell n) => (r, c) ∈ s) (layer_column_eq π f c)
  simpa [colUsed] using h

theorem rowUsed_union {n : ℕ} (A B : Finset (Cell n)) (r : Fin n) :
    rowUsed (A ∪ B) r = rowUsed A r ∪ rowUsed B r := by
  ext c
  simp [rowUsed]

theorem colUsed_union {n : ℕ} (A B : Finset (Cell n)) (c : Fin n) :
    colUsed (A ∪ B) c = colUsed A c ∪ colUsed B c := by
  ext r
  simp [colUsed]

/-- Reserving the constructed layer increases every row and column load by
at most two, so the matching can be reapplied with the updated budget. -/
theorem layer_load_update {n L : ℕ} (π f : Equiv.Perm (Fin n))
    (reserved : Finset (Cell n))
    (hrow : ∀ r, (rowUsed reserved r).card ≤ L)
    (hcol : ∀ c, (colUsed reserved c).card ≤ L) :
    (∀ r, (rowUsed (reserved ∪ layerCells π f) r).card ≤ L + 2) ∧
    (∀ c, (colUsed (reserved ∪ layerCells π f) c).card ≤ L + 2) := by
  constructor
  · intro r
    rw [rowUsed_union, rowUsed_layer_eq]
    have hcard := Finset.card_union_le (rowUsed reserved r) ({f r, f (π.symm r)} : Finset (Fin n))
    have htwo : ({f r, f (π.symm r)} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
    have hr := hrow r
    omega
  · intro c
    rw [colUsed_union, colUsed_layer_eq]
    have hcard := Finset.card_union_le (colUsed reserved c) ({f.symm c, π (f.symm c)} : Finset (Fin n))
    have htwo : ({f.symm c, π (f.symm c)} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
    have hc := hcol c
    omega

/-- Two successive derangement layers can be packed without reusing a cell.
The second matching is run after charging the first layer's two cells per
row and column to the reservation budget. -/
theorem physical_two_layers {n L : ℕ} (π₁ π₂ : Equiv.Perm (Fin n))
    (hd₁ : ∀ i, π₁ i ≠ i) (hd₂ : ∀ i, π₂ i ≠ i)
    (reserved : Finset (Cell n))
    (hrow : ∀ i, (rowUsed reserved i).card ≤ L)
    (hcol : ∀ j, (colUsed reserved j).card ≤ L)
    (hn : 4 * (L + 2) + 8 < n) :
    ∃ f₁ f₂ : Equiv.Perm (Fin n),
      Disjoint (layerCells π₁ f₁) (layerCells π₂ f₂) ∧
      (∀ z ∈ layerCells π₁ f₁, z ∉ reserved ∧ z ∉ mainCells n ∧ z ∉ antiCells n) ∧
      (∀ z ∈ layerCells π₂ f₂, z ∉ reserved ∧ z ∉ mainCells n ∧ z ∉ antiCells n) ∧
      (∀ r, ((layerCells π₁ f₁).filter (fun z => z.1 = r)).card = 2 ∧
        ((layerCells π₂ f₂).filter (fun z => z.1 = r)).card = 2) ∧
      (∀ c, ((layerCells π₁ f₁).filter (fun z => z.2 = c)).card = 2 ∧
        ((layerCells π₂ f₂).filter (fun z => z.2 = c)).card = 2) := by
  have hn₁ : 4 * L + 8 < n := by omega
  obtain ⟨f₁, _, hsafe₁, _, hrows₁, hcols₁⟩ :=
    physical_balanced_layer π₁ hd₁ reserved hrow hcol hn₁
  obtain ⟨hrow₂, hcol₂⟩ := layer_load_update π₁ f₁ reserved hrow hcol
  obtain ⟨f₂, _, hsafe₂, _, hrows₂, hcols₂⟩ :=
    physical_balanced_layer π₂ hd₂ (reserved ∪ layerCells π₁ f₁) hrow₂ hcol₂ hn
  refine ⟨f₁, f₂, ?_, hsafe₁, ?_, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro z hz₁ hz₂
    exact (hsafe₂ z hz₂).1 (Finset.mem_union_right reserved hz₁)
  · intro z hz
    have hs := hsafe₂ z hz
    refine ⟨?_, hs.2.1, hs.2.2⟩
    intro hr
    exact hs.1 (Finset.mem_union_left _ hr)
  · intro r
    exact ⟨hrows₁ r, hrows₂ r⟩
  · intro c
    exact ⟨hcols₁ c, hcols₂ c⟩

end
end Sude.LayerPacking
