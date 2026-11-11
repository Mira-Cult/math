import Sude.DisjointTrades
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Tactic.NormNum

/-! RP1: exact packing of both labelled diagonal rectangle families. -/
namespace Sude
namespace RectanglePacking
noncomputable section

/-- One- and two-step cyclic permutations of the rectangle labels. -/
def next (J : ℕ) : Equiv.Perm (Fin J) := finRotate J

def nextTwo (J : ℕ) : Equiv.Perm (Fin J) := (next J).trans (next J)

theorem next_ne_self {J : ℕ} (hJ : 3 ≤ J) (i : Fin J) : next J i ≠ i := by
  have : NeZero J := ⟨by omega⟩
  rw [next, finRotate_apply]
  intro h
  have hzero : (1 : Fin J) = 0 := add_left_cancel (show i + 1 = i + 0 by simpa using h)
  have hval : ((1 : Fin J) : ℕ) = 1 := by
    rw [Fin.val_one']
    exact Nat.mod_eq_of_lt (by omega)
  have hbad := congrArg Fin.val hzero
  change ((1 : Fin J) : ℕ) = 0 at hbad
  rw [hval] at hbad
  omega

theorem nextTwo_ne_self {J : ℕ} (hJ : 3 ≤ J) (i : Fin J) : nextTwo J i ≠ i := by
  have : NeZero J := ⟨by omega⟩
  intro h
  have heq : (i + 1) + 1 = i := by simpa [nextTwo, next, finRotate_apply] using h
  have htwo : (2 : Fin J) = 0 := by
    apply add_left_cancel (a := i)
    calc
      i + 2 = (i + 1) + 1 := by
        rw [add_assoc]
        congr 1
        apply Fin.ext
        change 2 % J = ((1 % J) + (1 % J)) % J
        simp [Nat.mod_eq_of_lt (show 1 < J by omega),
          Nat.mod_eq_of_lt (show 2 < J by omega)]
      _ = i := heq
      _ = i + 0 := by simp
  have hval : ((2 : Fin J) : ℕ) = 2 := by
    change 2 % J = 2
    exact Nat.mod_eq_of_lt (by omega)
  have hbad := congrArg Fin.val htwo
  change ((2 : Fin J) : ℕ) = 0 at hbad
  rw [hval] at hbad
  omega

theorem nextTwo_ne_next {J : ℕ} (hJ : 3 ≤ J) (i : Fin J) :
    nextTwo J i ≠ next J i := by
  intro h
  have h' : next J (next J i) = next J i := by simpa [nextTwo] using h
  exact next_ne_self hJ (next J i) h'

/-- Embed a rectangle label in the first half of the square. -/
def low {J n : ℕ} (hs : 2 * J + 1 ≤ n) (i : Fin J) : Fin n :=
  ⟨i.val, by have hi := i.isLt; omega⟩

@[simp] theorem low_val {J n : ℕ} (hs : 2 * J + 1 ≤ n) (i : Fin J) :
    (low hs i).val = i.val := rfl

theorem low_injective {J n : ℕ} (hs : 2 * J + 1 ≤ n) :
    Function.Injective (low hs) := by
  intro i j h
  apply Fin.ext
  simpa only [low_val] using congrArg (fun z : Fin n => z.val) h

/-- First-half labels and their reflections occupy disjoint halves. -/
theorem low_ne_rev_low {J n : ℕ} (hs : 2 * J + 1 ≤ n) (i j : Fin J) :
    low hs i ≠ (low hs j).rev := by
  intro h
  have hv := congrArg Fin.val h
  simp only [low_val, Fin.val_rev] at hv
  have hi := i.isLt
  have hj := j.isLt
  omega

theorem low_ne_center {J n : ℕ} (hs : 2 * J + 1 ≤ n) (hn : 0 < n)
    (i : Fin J) : low hs i ≠ centerIndex n hn := by
  intro h
  have hv := congrArg Fin.val h
  change i.val = n / 2 at hv
  have hi := i.isLt
  omega

theorem rev_low_ne_center {J n : ℕ} (hs : 2 * J + 1 ≤ n) (hn : 0 < n)
    (i : Fin J) : (low hs i).rev ≠ centerIndex n hn := by
  intro h
  have hv := congrArg Fin.val h
  change n - (i.val + 1) = n / 2 at hv
  have hi := i.isLt
  omega

/-- `true` prescribes the main diagonal; `false` the antidiagonal. -/
def designated {J n : ℕ} (hs : 2 * J + 1 ≤ n) (choice : Fin J → Bool)
    (i : Fin J) : Fin n :=
  if choice i then low hs i else (low hs i).rev

def firstRow {J n : ℕ} (hs : 2 * J + 1 ≤ n) (i : Fin J) : Fin n := low hs i

def secondRow {J n : ℕ} (hs : 2 * J + 1 ≤ n) (i : Fin J) : Fin n :=
  (low hs (next J i)).rev

def firstColumn {J n : ℕ} (hs : 2 * J + 1 ≤ n) (choice : Fin J → Bool)
    (i : Fin J) : Fin n := designated hs choice i

def secondColumn {J n : ℕ} (hs : 2 * J + 1 ≤ n) (choice : Fin J → Bool)
    (i : Fin J) : Fin n := (designated hs choice (nextTwo J i)).rev

/-- Choosing one side of each distinct mirror pair is injective. -/
theorem designated_injective {J n : ℕ} (hs : 2 * J + 1 ≤ n)
    (choice : Fin J → Bool) : Function.Injective (designated hs choice) := by
  intro i j h
  cases hi : choice i <;> cases hj : choice j
  · have he : low hs i = low hs j := by simpa [designated, hi, hj] using h
    exact low_injective hs he
  · have he : (low hs i).rev = low hs j := by simpa [designated, hi, hj] using h
    exact False.elim (low_ne_rev_low hs j i he.symm)
  · have he : low hs i = (low hs j).rev := by simpa [designated, hi, hj] using h
    exact False.elim (low_ne_rev_low hs i j he)
  · have he : low hs i = low hs j := by simpa [designated, hi, hj] using h
    exact low_injective hs he

/-- Chosen sides and their reflected sides are disjoint, even for arbitrary
    mixtures of main and antidiagonal prescriptions. -/
theorem designated_ne_rev_designated {J n : ℕ} (hs : 2 * J + 1 ≤ n)
    (choice : Fin J → Bool) (i j : Fin J) :
    designated hs choice i ≠ (designated hs choice j).rev := by
  intro h
  cases hi : choice i <;> cases hj : choice j
  · have he : (low hs i).rev = low hs j := by simpa [designated, hi, hj] using h
    exact low_ne_rev_low hs j i he.symm
  · have he : low hs i = low hs j := by simpa [designated, hi, hj] using h
    have hij : i = j := low_injective hs he
    subst j
    simp_all
  · have he : low hs i = low hs j := by simpa [designated, hi, hj] using h
    have hij : i = j := low_injective hs he
    subst j
    simp_all
  · have he : low hs i = (low hs j).rev := by simpa [designated, hi, hj] using h
    exact low_ne_rev_low hs i j he

theorem firstRow_injective {J n : ℕ} (hs : 2 * J + 1 ≤ n) :
    Function.Injective (firstRow hs) := low_injective hs

theorem secondRow_injective {J n : ℕ} (hs : 2 * J + 1 ≤ n) :
    Function.Injective (secondRow hs) := by
  intro i j h
  apply (next J).injective
  apply low_injective hs
  exact Fin.rev_inj.mp h

theorem firstRow_ne_secondRow {J n : ℕ} (hs : 2 * J + 1 ≤ n)
    (i j : Fin J) : firstRow hs i ≠ secondRow hs j :=
  low_ne_rev_low hs i (next J j)

theorem firstColumn_injective {J n : ℕ} (hs : 2 * J + 1 ≤ n)
    (choice : Fin J → Bool) : Function.Injective (firstColumn hs choice) :=
  designated_injective hs choice

theorem secondColumn_injective {J n : ℕ} (hs : 2 * J + 1 ≤ n)
    (choice : Fin J → Bool) : Function.Injective (secondColumn hs choice) := by
  intro i j h
  apply (nextTwo J).injective
  apply designated_injective hs choice
  exact Fin.rev_inj.mp h

theorem firstColumn_ne_secondColumn {J n : ℕ} (hs : 2 * J + 1 ≤ n)
    (choice : Fin J → Bool) (i j : Fin J) :
    firstColumn hs choice i ≠ secondColumn hs choice j :=
  designated_ne_rev_designated hs choice i (nextTwo J j)

/-- The two row slots and the two column slots are each globally injective. -/
def rowSlot {J n : ℕ} (hs : 2 * J + 1 ≤ n) (p : Fin J × Bool) : Fin n :=
  if p.2 then firstRow hs p.1 else secondRow hs p.1

def columnSlot {J n : ℕ} (hs : 2 * J + 1 ≤ n) (choice : Fin J → Bool)
    (p : Fin J × Bool) : Fin n :=
  if p.2 then firstColumn hs choice p.1 else secondColumn hs choice p.1

theorem rowSlot_injective {J n : ℕ} (hs : 2 * J + 1 ≤ n) :
    Function.Injective (rowSlot hs) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  cases b <;> cases c
  · have he : secondRow hs i = secondRow hs j := by simpa [rowSlot] using h
    have : i = j := secondRow_injective hs he
    subst j
    rfl
  · have he : secondRow hs i = firstRow hs j := by simpa [rowSlot] using h
    exact False.elim (firstRow_ne_secondRow hs j i he.symm)
  · have he : firstRow hs i = secondRow hs j := by simpa [rowSlot] using h
    exact False.elim (firstRow_ne_secondRow hs i j he)
  · have he : firstRow hs i = firstRow hs j := by simpa [rowSlot] using h
    have : i = j := firstRow_injective hs he
    subst j
    rfl

theorem columnSlot_injective {J n : ℕ} (hs : 2 * J + 1 ≤ n)
    (choice : Fin J → Bool) : Function.Injective (columnSlot hs choice) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  cases b <;> cases c
  · have he : secondColumn hs choice i = secondColumn hs choice j := by
      simpa [columnSlot] using h
    have : i = j := secondColumn_injective hs choice he
    subst j
    rfl
  · have he : secondColumn hs choice i = firstColumn hs choice j := by
      simpa [columnSlot] using h
    exact False.elim (firstColumn_ne_secondColumn hs choice j i he.symm)
  · have he : firstColumn hs choice i = secondColumn hs choice j := by
      simpa [columnSlot] using h
    exact False.elim (firstColumn_ne_secondColumn hs choice i j he)
  · have he : firstColumn hs choice i = firstColumn hs choice j := by
      simpa [columnSlot] using h
    have : i = j := firstColumn_injective hs choice he
    subst j
    rfl

/-- The second column meets neither diagonal in the first row. -/
theorem firstRow_secondColumn_off_diagonals {J n : ℕ}
    (hs : 2 * J + 1 ≤ n) (hJ : 3 ≤ J) (choice : Fin J → Bool) (i : Fin J) :
    (firstRow hs i, secondColumn hs choice i) ∉ mainCells n ∧
    (firstRow hs i, secondColumn hs choice i) ∉ antiCells n := by
  have hσ : low hs (nextTwo J i) ≠ low hs i := by
    intro h
    exact nextTwo_ne_self hJ i (low_injective hs h)
  have hcross := low_ne_rev_low hs i (nextTwo J i)
  have hcross' := low_ne_rev_low hs (nextTwo J i) i
  cases hc : choice (nextTwo J i)
  · simp [firstRow, secondColumn, designated, hc, Ne.symm hσ, hcross']
  · simp [firstRow, secondColumn, designated, hc, hσ, hcross]

/-- The first column meets neither diagonal in the second row. -/
theorem secondRow_firstColumn_off_diagonals {J n : ℕ}
    (hs : 2 * J + 1 ≤ n) (hJ : 3 ≤ J) (choice : Fin J → Bool) (i : Fin J) :
    (secondRow hs i, firstColumn hs choice i) ∉ mainCells n ∧
    (secondRow hs i, firstColumn hs choice i) ∉ antiCells n := by
  have hπ : low hs (next J i) ≠ low hs i := by
    intro h
    exact next_ne_self hJ i (low_injective hs h)
  have hcross := low_ne_rev_low hs i (next J i)
  have hcross' := low_ne_rev_low hs (next J i) i
  cases hc : choice i
  · simp [secondRow, firstColumn, designated, hc, hπ, Ne.symm hcross']
  · simp [secondRow, firstColumn, designated, hc, Ne.symm hπ, Ne.symm hcross]

/-- The remaining corner meets neither diagonal. -/
theorem secondRow_secondColumn_off_diagonals {J n : ℕ}
    (hs : 2 * J + 1 ≤ n) (hJ : 3 ≤ J) (choice : Fin J → Bool) (i : Fin J) :
    (secondRow hs i, secondColumn hs choice i) ∉ mainCells n ∧
    (secondRow hs i, secondColumn hs choice i) ∉ antiCells n := by
  have hσπ : low hs (nextTwo J i) ≠ low hs (next J i) := by
    intro h
    exact nextTwo_ne_next hJ i (low_injective hs h)
  have hcross := low_ne_rev_low hs (next J i) (nextTwo J i)
  have hcross' := low_ne_rev_low hs (nextTwo J i) (next J i)
  cases hc : choice (nextTwo J i)
  · simp [secondRow, secondColumn, designated, hc, hσπ, Ne.symm hcross']
  · simp [secondRow, secondColumn, designated, hc, Ne.symm hσπ, Ne.symm hcross]

/-- The designated corner lies on exactly its prescribed diagonal. -/
theorem designated_corner_geometry {J n : ℕ} (hs : 2 * J + 1 ≤ n)
    (choice : Fin J → Bool) (i : Fin J) :
    (choice i = true → (firstRow hs i, firstColumn hs choice i) ∈ mainCells n ∧
      (firstRow hs i, firstColumn hs choice i) ∉ antiCells n) ∧
    (choice i = false → (firstRow hs i, firstColumn hs choice i) ∈ antiCells n ∧
      (firstRow hs i, firstColumn hs choice i) ∉ mainCells n) := by
  have hc := low_ne_rev_low hs i i
  cases h : choice i
  · simp [firstRow, firstColumn, designated, h, hc]
  · simp [firstRow, firstColumn, designated, h, hc]

/-- None of the four cells is the center, since neither used row is central. -/
theorem rectangle_avoids_center {J n : ℕ} (hs : 2 * J + 1 ≤ n)
    (hn : 0 < n) (choice : Fin J → Bool) (i : Fin J) :
    (centerIndex n hn, centerIndex n hn) ∉
      rectangleCells (firstRow hs i) (secondRow hs i)
        (firstColumn hs choice i) (secondColumn hs choice i) := by
  intro hm
  have h1 : firstRow hs i ≠ centerIndex n hn := low_ne_center hs hn i
  have h2 : secondRow hs i ≠ centerIndex n hn := rev_low_ne_center hs hn (next J i)
  rcases (mem_rectangleCells _ _ _ _ _).mp hm with h | h | h | h
  · exact h1 (congrArg Prod.fst h).symm
  · exact h1 (congrArg Prod.fst h).symm
  · exact h2 (congrArg Prod.fst h).symm
  · exact h2 (congrArg Prod.fst h).symm

/-- Different rectangle labels have disjoint physical cell supports. -/
theorem rectangle_cells_disjoint {J n : ℕ} (hs : 2 * J + 1 ≤ n)
    (choice : Fin J → Bool) (i j : Fin J) (hne : i ≠ j) :
    Disjoint
      (rectangleCells (firstRow hs i) (secondRow hs i)
        (firstColumn hs choice i) (secondColumn hs choice i))
      (rectangleCells (firstRow hs j) (secondRow hs j)
        (firstColumn hs choice j) (secondColumn hs choice j)) := by
  apply Finset.disjoint_left.mpr
  intro t hi hj
  have hli : t.1 = firstRow hs i ∨ t.1 = secondRow hs i := by
    rcases (mem_rectangleCells _ _ _ _ _).mp hi with h | h | h | h
    · exact Or.inl (congrArg Prod.fst h)
    · exact Or.inl (congrArg Prod.fst h)
    · exact Or.inr (congrArg Prod.fst h)
    · exact Or.inr (congrArg Prod.fst h)
  have hlj : t.1 = firstRow hs j ∨ t.1 = secondRow hs j := by
    rcases (mem_rectangleCells _ _ _ _ _).mp hj with h | h | h | h
    · exact Or.inl (congrArg Prod.fst h)
    · exact Or.inl (congrArg Prod.fst h)
    · exact Or.inr (congrArg Prod.fst h)
    · exact Or.inr (congrArg Prod.fst h)
  rcases hli with hi1 | hi2 <;> rcases hlj with hj1 | hj2
  · exact hne (firstRow_injective hs (hi1.symm.trans hj1))
  · exact firstRow_ne_secondRow hs i j (hi1.symm.trans hj2)
  · exact firstRow_ne_secondRow hs j i (hj1.symm.trans hi2)
  · exact hne (secondRow_injective hs (hi2.symm.trans hj2))

/-- The construction occupies exactly 2J distinct rows and columns. -/
theorem rowSlot_card {J n : ℕ} (hs : 2 * J + 1 ≤ n) :
    (Finset.univ.image (rowSlot hs)).card = 2 * J := by
  rw [Finset.card_image_of_injective _ (rowSlot_injective hs)]
  simp [Fintype.card_prod, Nat.mul_comm]

theorem columnSlot_card {J n : ℕ} (hs : 2 * J + 1 ≤ n)
    (choice : Fin J → Bool) :
    (Finset.univ.image (columnSlot hs choice)).card = 2 * J := by
  rw [Finset.card_image_of_injective _ (columnSlot_injective hs choice)]
  simp [Fintype.card_prod, Nat.mul_comm]

/-- Each packed rectangle has four distinct physical cells. -/
theorem rectangle_four_cells {J n : ℕ} (hs : 2 * J + 1 ≤ n)
    (choice : Fin J → Bool) (i : Fin J) :
    (rectangleCells (firstRow hs i) (secondRow hs i)
      (firstColumn hs choice i) (secondColumn hs choice i)).card = 4 := by
  have hr := firstRow_ne_secondRow hs i i
  have hc := firstColumn_ne_secondColumn hs choice i i
  simp [rectangleCells, Prod.mk.injEq, hr, hc, Ne.symm hc]

/-- Full source construction RP1. The row/column slot maps are globally
    injective; every non-designated corner avoids both diagonals, the center
    is unused, and different rectangles have disjoint physical cells. -/
theorem rp1_exact_packing {J n : ℕ} (hs : 2 * J + 1 ≤ n) (hJ : 3 ≤ J)
    (choice : Fin J → Bool) :
    Function.Injective (rowSlot hs) ∧
    Function.Injective (columnSlot hs choice) ∧
    (Finset.univ.image (rowSlot hs)).card = 2 * J ∧
    (Finset.univ.image (columnSlot hs choice)).card = 2 * J ∧
    (∀ i, firstRow hs i ≠ secondRow hs i ∧
      firstColumn hs choice i ≠ secondColumn hs choice i ∧
      (rectangleCells (firstRow hs i) (secondRow hs i)
        (firstColumn hs choice i) (secondColumn hs choice i)).card = 4 ∧
      (choice i = true → (firstRow hs i, firstColumn hs choice i) ∈ mainCells n ∧
        (firstRow hs i, firstColumn hs choice i) ∉ antiCells n) ∧
      (choice i = false → (firstRow hs i, firstColumn hs choice i) ∈ antiCells n ∧
        (firstRow hs i, firstColumn hs choice i) ∉ mainCells n) ∧
      ((firstRow hs i, secondColumn hs choice i) ∉ mainCells n ∧
        (firstRow hs i, secondColumn hs choice i) ∉ antiCells n) ∧
      ((secondRow hs i, firstColumn hs choice i) ∉ mainCells n ∧
        (secondRow hs i, firstColumn hs choice i) ∉ antiCells n) ∧
      ((secondRow hs i, secondColumn hs choice i) ∉ mainCells n ∧
        (secondRow hs i, secondColumn hs choice i) ∉ antiCells n) ∧
      (∀ hn : 0 < n, (centerIndex n hn, centerIndex n hn) ∉
        rectangleCells (firstRow hs i) (secondRow hs i)
          (firstColumn hs choice i) (secondColumn hs choice i))) ∧
    (∀ i j, i ≠ j → Disjoint
      (rectangleCells (firstRow hs i) (secondRow hs i)
        (firstColumn hs choice i) (secondColumn hs choice i))
      (rectangleCells (firstRow hs j) (secondRow hs j)
        (firstColumn hs choice j) (secondColumn hs choice j))) := by
  refine ⟨rowSlot_injective hs, columnSlot_injective hs choice,
    rowSlot_card hs, columnSlot_card hs choice, ?_, ?_⟩
  · intro i
    exact ⟨firstRow_ne_secondRow hs i i, firstColumn_ne_secondColumn hs choice i i,
      rectangle_four_cells hs choice i, (designated_corner_geometry hs choice i).1,
      (designated_corner_geometry hs choice i).2,
      firstRow_secondColumn_off_diagonals hs hJ choice i,
      secondRow_firstColumn_off_diagonals hs hJ choice i,
      secondRow_secondColumn_off_diagonals hs hJ choice i,
      fun hn => rectangle_avoids_center hs hn choice i⟩
  · intro i j hij
    exact rectangle_cells_disjoint hs choice i j hij

/-- The RP1 coordinates discharge the geometry and disjointness premises
    of the physical main-then-antidiagonal trade. The equal-gap entries
    remain explicit hypotheses and must still be supplied by the controller. -/
theorem packed_main_then_anti {J n : ℕ} (hs : 2 * J + 1 ≤ n) (hJ : 3 ≤ J)
    (choice : Fin J → Bool) (i j : Fin J) (hne : i ≠ j)
    (hmain : choice i = true) (hanti : choice j = false)
    (a : Cell n ≃ Fin (n * n)) (h h' : ℕ)
    (top : entry a (firstRow hs i, secondColumn hs choice i) =
      entry a (firstRow hs i, firstColumn hs choice i) + h)
    (bottom : entry a (secondRow hs i, firstColumn hs choice i) =
      entry a (secondRow hs i, secondColumn hs choice i) + h)
    (top' : entry a (firstRow hs j, secondColumn hs choice j) =
      entry a (firstRow hs j, firstColumn hs choice j) + h')
    (bottom' : entry a (secondRow hs j, firstColumn hs choice j) =
      entry a (secondRow hs j, secondColumn hs choice j) + h') :
    let result := rectangleTrade
      (rectangleTrade a (firstRow hs i) (secondRow hs i)
        (firstColumn hs choice i) (secondColumn hs choice i))
      (firstRow hs j) (secondRow hs j)
      (firstColumn hs choice j) (secondColumn hs choice j)
    (∀ r, rowSum result r = rowSum a r) ∧
    (∀ r, columnSum result r = columnSum a r) ∧
    (mainSum result : ℤ) = (mainSum a : ℤ) + h ∧
    (antiSum result : ℤ) = (antiSum a : ℤ) + h' ∧
    Set.range (entry result) = pool n ∧ Function.Injective (entry result) := by
  have mainCorner := (designated_corner_geometry hs choice i).1 hmain
  have antiCorner := (designated_corner_geometry hs choice j).2 hanti
  have io1 := firstRow_secondColumn_off_diagonals hs hJ choice i
  have io2 := secondRow_firstColumn_off_diagonals hs hJ choice i
  have io3 := secondRow_secondColumn_off_diagonals hs hJ choice i
  have jo1 := firstRow_secondColumn_off_diagonals hs hJ choice j
  have jo2 := secondRow_firstColumn_off_diagonals hs hJ choice j
  have jo3 := secondRow_secondColumn_off_diagonals hs hJ choice j
  exact rectangleTrade_main_then_anti a
    (firstRow hs i) (secondRow hs i) (firstColumn hs choice i) (secondColumn hs choice i)
    (firstRow hs j) (secondRow hs j) (firstColumn hs choice j) (secondColumn hs choice j)
    h h' (rectangle_cells_disjoint hs choice i j hne)
    (firstRow_ne_secondRow hs i i) (firstColumn_ne_secondColumn hs choice i i)
    (firstRow_ne_secondRow hs j j) (firstColumn_ne_secondColumn hs choice j j)
    top bottom top' bottom' mainCorner.1 io1.1 io2.1 io3.1
    mainCorner.2 io1.2 io2.2 io3.2 antiCorner.1 jo1.2 jo2.2 jo3.2
    antiCorner.2 jo1.1 jo2.1 jo3.1

/-- Both RP1 rectangles leave the common center untouched. -/
theorem packed_main_then_anti_center {J n : ℕ} (hs : 2 * J + 1 ≤ n) (hJ : 3 ≤ J)
    (choice : Fin J → Bool) (i j : Fin J)
    (hmain : choice i = true) (hanti : choice j = false)
    (a : Cell n ≃ Fin (n * n)) (hn : 0 < n) (hodd : Odd n) :
    entry (rectangleTrade
      (rectangleTrade a (firstRow hs i) (secondRow hs i)
        (firstColumn hs choice i) (secondColumn hs choice i))
      (firstRow hs j) (secondRow hs j)
      (firstColumn hs choice j) (secondColumn hs choice j))
      (centerIndex n hn, centerIndex n hn) =
      entry a (centerIndex n hn, centerIndex n hn) := by
  have mainCorner := (designated_corner_geometry hs choice i).1 hmain
  have antiCorner := (designated_corner_geometry hs choice j).2 hanti
  have io1 := firstRow_secondColumn_off_diagonals hs hJ choice i
  have io2 := secondRow_firstColumn_off_diagonals hs hJ choice i
  have io3 := secondRow_secondColumn_off_diagonals hs hJ choice i
  have jo1 := firstRow_secondColumn_off_diagonals hs hJ choice j
  have jo2 := secondRow_firstColumn_off_diagonals hs hJ choice j
  have jo3 := secondRow_secondColumn_off_diagonals hs hJ choice j
  exact rectangleTrade_main_then_anti_center a
    (firstRow hs i) (secondRow hs i) (firstColumn hs choice i) (secondColumn hs choice i)
    (firstRow hs j) (secondRow hs j) (firstColumn hs choice j) (secondColumn hs choice j)
    hn hodd mainCorner.2 io1.2 io2.2 io3.2 antiCorner.2 jo1.1 jo2.1 jo3.1

end
end RectanglePacking
end Sude
