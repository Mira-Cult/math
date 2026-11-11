import Sude.RectanglePacking
import Mathlib.Logic.Equiv.Fintype

/-! Extend any distinct prescribed pool entries at distinct physical cells
    to a full exact-pool permutation. No prime supply is assumed. -/
namespace Sude
noncomputable section

/-- Every finite injective assignment of actual pool members to distinct
    cells extends to a bijective placement of the complete original pool. -/
theorem place_distinct_pool_entries {n : ℕ} {α : Type*} [Finite α]
    (a : Cell n ≃ Fin (n * n)) (cells : α → Cell n) (values : α → pool n)
    (hcells : Function.Injective cells) (hvalues : Function.Injective values) :
    ∃ a' : Cell n ≃ Fin (n * n),
      ∀ t, entry a' (cells t) = (values t).val := by
  let target : α → Cell n := fun t => a.symm ((poolEquiv n).symm (values t))
  have htarget : Function.Injective target :=
    a.symm.injective.comp ((poolEquiv n).symm.injective.comp hvalues)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair cells target hcells htarget
  refine ⟨σ.trans a, ?_⟩
  intro t
  simp [entry, Equiv.trans_apply, hσ, target]

/-- Extend new assignments while retaining every previously reserved cell.
    The caller must prove that new cells and values avoid those reservations. -/
theorem place_distinct_pool_entries_preserving {n : ℕ} {α : Type*} [Finite α]
    (a : Cell n ≃ Fin (n * n)) (cells : α → Cell n) (values : α → pool n)
    (reserved : Finset (Cell n))
    (hcells : Function.Injective cells) (hvalues : Function.Injective values)
    (hnew : ∀ t, cells t ∉ reserved)
    (havoid : ∀ t c, c ∈ reserved → (values t).val ≠ entry a c) :
    ∃ a' : Cell n ≃ Fin (n * n),
      (∀ t, entry a' (cells t) = (values t).val) ∧
      (∀ c ∈ reserved, entry a' c = entry a c) := by
  classical
  let : Fintype α := Fintype.ofFinite α
  let oldValue : {c : Cell n // c ∈ reserved} → pool n := fun c =>
    ⟨entry a c.val, ⟨a c.val, rfl⟩⟩
  let allCells : α ⊕ {c : Cell n // c ∈ reserved} → Cell n :=
    Sum.elim cells Subtype.val
  let allValues : α ⊕ {c : Cell n // c ∈ reserved} → pool n :=
    Sum.elim values oldValue
  have hAllCells : Function.Injective allCells := by
    intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        have hxy : cells x = cells y := h
        exact congrArg Sum.inl (hcells hxy)
      | inr y =>
        have hxy : cells x = y.val := h
        exact False.elim (hnew x (hxy ▸ y.property))
    | inr x =>
      cases y with
      | inl y =>
        have hxy : x.val = cells y := h
        exact False.elim (hnew y (hxy ▸ x.property))
      | inr y =>
        have hxy : x.val = y.val := h
        exact congrArg Sum.inr (Subtype.ext hxy)
  have hOld : Function.Injective oldValue := by
    intro x y h
    apply Subtype.ext
    apply entry_injective a
    exact congrArg Subtype.val h
  have hAllValues : Function.Injective allValues := by
    intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        have hxy : values x = values y := h
        exact congrArg Sum.inl (hvalues hxy)
      | inr y =>
        have hxy : (values x).val = entry a y.val := congrArg Subtype.val h
        exact False.elim (havoid x y.val y.property hxy)
    | inr x =>
      cases y with
      | inl y =>
        have hxy : entry a x.val = (values y).val := congrArg Subtype.val h
        exact False.elim (havoid y x.val x.property hxy.symm)
      | inr y =>
        have hxy : oldValue x = oldValue y := h
        exact congrArg Sum.inr (hOld hxy)
  obtain ⟨a', hplace⟩ :=
    place_distinct_pool_entries a allCells allValues hAllCells hAllValues
  refine ⟨a', ?_, ?_⟩
  · intro t
    exact hplace (Sum.inl t)
  · intro c hc
    exact hplace (Sum.inr ⟨c, hc⟩)

namespace RectanglePacking

/-- A rectangle label and two binary side choices determine an actual cell. -/
def cornerSlot {J n : ℕ} (hs : 2 * J + 1 ≤ n) (choice : Fin J → Bool)
    (p : Fin J × Bool × Bool) : Cell n :=
  (rowSlot hs (p.1, p.2.1), columnSlot hs choice (p.1, p.2.2))

/-- Every one of the 4J physical slots is distinct. -/
theorem cornerSlot_injective {J n : ℕ} (hs : 2 * J + 1 ≤ n)
    (choice : Fin J → Bool) : Function.Injective (cornerSlot hs choice) := by
  rintro ⟨i, r, c⟩ ⟨j, r', c'⟩ h
  have hr : (i, r) = (j, r') := rowSlot_injective hs (congrArg Prod.fst h)
  have hc : (i, c) = (j, c') := columnSlot_injective hs choice (congrArg Prod.snd h)
  have hij : i = j := congrArg Prod.fst hr
  have hrr : r = r' := congrArg Prod.snd hr
  have hcc : c = c' := congrArg Prod.snd hc
  subst j
  subst r'
  subst c'
  rfl

@[simp] theorem cornerSlot_tt {J n : ℕ} (hs : 2 * J + 1 ≤ n)
    (choice : Fin J → Bool) (i : Fin J) :
    cornerSlot hs choice (i, true, true) = (firstRow hs i, firstColumn hs choice i) := by
  simp [cornerSlot, rowSlot, columnSlot]

@[simp] theorem cornerSlot_tf {J n : ℕ} (hs : 2 * J + 1 ≤ n)
    (choice : Fin J → Bool) (i : Fin J) :
    cornerSlot hs choice (i, true, false) = (firstRow hs i, secondColumn hs choice i) := by
  simp [cornerSlot, rowSlot, columnSlot]

@[simp] theorem cornerSlot_ft {J n : ℕ} (hs : 2 * J + 1 ≤ n)
    (choice : Fin J → Bool) (i : Fin J) :
    cornerSlot hs choice (i, false, true) = (secondRow hs i, firstColumn hs choice i) := by
  simp [cornerSlot, rowSlot, columnSlot]

@[simp] theorem cornerSlot_ff {J n : ℕ} (hs : 2 * J + 1 ≤ n)
    (choice : Fin J → Bool) (i : Fin J) :
    cornerSlot hs choice (i, false, false) = (secondRow hs i, secondColumn hs choice i) := by
  simp [cornerSlot, rowSlot, columnSlot]

/-- The corner-slot domain covers exactly 4J distinct physical cells. -/
theorem cornerSlot_card {J n : ℕ} (hs : 2 * J + 1 ≤ n)
    (choice : Fin J → Bool) :
    (Finset.univ.image (cornerSlot hs choice)).card = 4 * J := by
  rw [Finset.card_image_of_injective _ (cornerSlot_injective hs choice)]
  simp [Fintype.card_prod, Nat.mul_comm]

/-- The slot encoding covers exactly the union of the constructed rectangles. -/
theorem cornerSlot_range_iff {J n : ℕ} (hs : 2 * J + 1 ≤ n)
    (choice : Fin J → Bool) (t : Cell n) :
    t ∈ Set.range (cornerSlot hs choice) ↔
      ∃ i, t ∈ rectangleCells (firstRow hs i) (secondRow hs i)
        (firstColumn hs choice i) (secondColumn hs choice i) := by
  constructor
  · rintro ⟨⟨i, r, c⟩, rfl⟩
    refine ⟨i, ?_⟩
    cases r <;> cases c <;> simp
  · rintro ⟨i, hi⟩
    rcases (mem_rectangleCells _ _ _ _ _).mp hi with h | h | h | h
    · exact ⟨(i, true, true), by simpa using h.symm⟩
    · exact ⟨(i, true, false), by simpa using h.symm⟩
    · exact ⟨(i, false, true), by simpa using h.symm⟩
    · exact ⟨(i, false, false), by simpa using h.symm⟩

/-- Distinct prescribed pool entries fill all RP1 rectangle slots and extend
    to a complete exact-pool permutation of the whole square. -/
theorem place_packed_entries {J n : ℕ} (hs : 2 * J + 1 ≤ n)
    (choice : Fin J → Bool) (a : Cell n ≃ Fin (n * n))
    (values : Fin J × Bool × Bool → pool n) (hvalues : Function.Injective values) :
    ∃ a' : Cell n ≃ Fin (n * n),
      ∀ t, entry a' (cornerSlot hs choice t) = (values t).val :=
  place_distinct_pool_entries a (cornerSlot hs choice) values
    (cornerSlot_injective hs choice) hvalues

/-- A trade at one packed rectangle leaves all disjoint reserved cells
    untouched, regardless of the values in the rectangle. -/
theorem packed_trade_preserves_reserved {J n : ℕ} (hs : 2 * J + 1 ≤ n)
    (choice : Fin J → Bool) (a : Cell n ≃ Fin (n * n)) (i : Fin J)
    (reserved : Finset (Cell n)) (hnew : ∀ t, cornerSlot hs choice t ∉ reserved) :
    ∀ c ∈ reserved,
      entry (rectangleTrade a (firstRow hs i) (secondRow hs i)
        (firstColumn hs choice i) (secondColumn hs choice i)) c = entry a c := by
  intro c hc
  have h1 := hnew (i, true, true)
  have h2 := hnew (i, true, false)
  have h3 := hnew (i, false, true)
  have h4 := hnew (i, false, false)
  simp only [cornerSlot_tt, cornerSlot_tf, cornerSlot_ft, cornerSlot_ff] at h1 h2 h3 h4
  apply rectangleTrade_outside
  · intro he; exact h1 (he ▸ hc)
  · intro he; exact h2 (he ▸ hc)
  · intro he; exact h3 (he ▸ hc)
  · intro he; exact h4 (he ▸ hc)

/-- Install pair entries in the actual packed rectangles while retaining
    every previously reserved cell and all entries of the original pool.
    Existence and distinctness of the supplied prime values are hypotheses. -/
theorem place_packed_pairs_preserving {J n : ℕ} (hs : 2 * J + 1 ≤ n)
    (choice : Fin J → Bool) (a : Cell n ≃ Fin (n * n))
    (values : Fin J × Bool × Bool → pool n) (gap : Fin J → ℕ)
    (reserved : Finset (Cell n)) (hvalues : Function.Injective values)
    (hnew : ∀ t, cornerSlot hs choice t ∉ reserved)
    (havoid : ∀ t c, c ∈ reserved → (values t).val ≠ entry a c)
    (htop : ∀ i, (values (i, true, false)).val = (values (i, true, true)).val + gap i)
    (hbottom : ∀ i, (values (i, false, true)).val = (values (i, false, false)).val + gap i) :
    ∃ a' : Cell n ≃ Fin (n * n),
      (∀ t, entry a' (cornerSlot hs choice t) = (values t).val) ∧
      (∀ c ∈ reserved, entry a' c = entry a c) ∧
      (∀ i, entry a' (firstRow hs i, secondColumn hs choice i) =
          entry a' (firstRow hs i, firstColumn hs choice i) + gap i ∧
        entry a' (secondRow hs i, firstColumn hs choice i) =
          entry a' (secondRow hs i, secondColumn hs choice i) + gap i) ∧
      Set.range (entry a') = pool n ∧ Function.Injective (entry a') := by
  obtain ⟨a', hplaced, hfixed⟩ := place_distinct_pool_entries_preserving a
    (cornerSlot hs choice) values reserved (cornerSlot_injective hs choice)
    hvalues hnew havoid
  refine ⟨a', hplaced, hfixed, ?_, entry_range _, entry_injective _⟩
  intro i
  have h1 := hplaced (i, true, true)
  have h2 := hplaced (i, true, false)
  have h3 := hplaced (i, false, true)
  have h4 := hplaced (i, false, false)
  simp only [cornerSlot_tt, cornerSlot_tf, cornerSlot_ft, cornerSlot_ff] at h1 h2 h3 h4
  exact ⟨by rw [h1, h2]; exact htop i, by rw [h3, h4]; exact hbottom i⟩

/-- End-to-end physical interface for two selected RP1 rectangles. The
    pre-trade completion and its remaining line sums are not assumed equal
    to the original partial placement's line sums. -/
theorem place_and_trade_packed_pairs {J n : ℕ} (hs : 2 * J + 1 ≤ n) (hJ : 3 ≤ J)
    (choice : Fin J → Bool) (i j : Fin J) (hne : i ≠ j)
    (hmain : choice i = true) (hanti : choice j = false)
    (a : Cell n ≃ Fin (n * n)) (values : Fin J × Bool × Bool → pool n)
    (gap : Fin J → ℕ) (reserved : Finset (Cell n))
    (hvalues : Function.Injective values)
    (hnew : ∀ t, cornerSlot hs choice t ∉ reserved)
    (havoid : ∀ t c, c ∈ reserved → (values t).val ≠ entry a c)
    (htop : ∀ z, (values (z, true, false)).val = (values (z, true, true)).val + gap z)
    (hbottom : ∀ z, (values (z, false, true)).val = (values (z, false, false)).val + gap z) :
    ∃ a' : Cell n ≃ Fin (n * n),
      let result := rectangleTrade
        (rectangleTrade a' (firstRow hs i) (secondRow hs i)
          (firstColumn hs choice i) (secondColumn hs choice i))
        (firstRow hs j) (secondRow hs j)
        (firstColumn hs choice j) (secondColumn hs choice j)
      (∀ t, entry a' (cornerSlot hs choice t) = (values t).val) ∧
      (∀ c ∈ reserved, entry a' c = entry a c ∧ entry result c = entry a c) ∧
      (∀ z, 0 < gap z) ∧
      (∀ r, rowSum result r = rowSum a' r) ∧
      (∀ r, columnSum result r = columnSum a' r) ∧
      (mainSum result : ℤ) = (mainSum a' : ℤ) + gap i ∧
      (antiSum result : ℤ) = (antiSum a' : ℤ) + gap j ∧
      Set.range (entry result) = pool n ∧ Function.Injective (entry result) ∧
      (∀ hn : 0 < n, Odd n →
        entry result (centerIndex n hn, centerIndex n hn) =
          entry a' (centerIndex n hn, centerIndex n hn)) := by
  obtain ⟨a', hplaced, hfixed, hgaps, _hpool, _hinj⟩ :=
    place_packed_pairs_preserving hs choice a values gap reserved hvalues hnew havoid htop hbottom
  have htrade := packed_main_then_anti hs hJ choice i j hne hmain hanti a' (gap i) (gap j)
    (hgaps i).1 (hgaps i).2 (hgaps j).1 (hgaps j).2
  dsimp only at htrade
  rcases htrade with ⟨hrows, hcols, hdiag, hanti', hpool, hinj⟩
  refine ⟨a', hplaced, ?_, ?_, hrows, hcols, hdiag, hanti', hpool, hinj, ?_⟩
  · intro c hc
    have hfirst := packed_trade_preserves_reserved hs choice a' i reserved hnew c hc
    have hsecond := packed_trade_preserves_reserved hs choice
      (rectangleTrade a' (firstRow hs i) (secondRow hs i)
        (firstColumn hs choice i) (secondColumn hs choice i)) j reserved hnew c hc
    exact ⟨hfixed c hc, hsecond.trans (hfirst.trans (hfixed c hc))⟩
  · intro z
    exact rectangleTrade_gap_positive a' (firstRow hs z) (firstColumn hs choice z)
      (secondColumn hs choice z) (gap z) (firstColumn_ne_secondColumn hs choice z z)
      (hgaps z).1
  · intro hn hodd
    exact packed_main_then_anti_center hs hJ choice i j hmain hanti a' hn hodd

end RectanglePacking
end
end Sude
