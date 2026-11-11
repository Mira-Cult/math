import Sude.Statement
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Linarith

/-! Physical permutations and line effects for the rectangle trade RP2.
No rectangle-packing, pair-supply, or global controller theorem is assumed. -/

namespace Sude
noncomputable section

/-- Swapping two actual cells composes the existing exact rank permutation
    with a permutation of its domain. -/
def swapPlacement {n : ℕ} (a : Cell n ≃ Fin (n * n)) (x y : Cell n) :
    Cell n ≃ Fin (n * n) := (Equiv.swap x y).trans a

@[simp] theorem entry_swapPlacement {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (x y t : Cell n) : entry (swapPlacement a x y) t = entry a ((Equiv.swap x y) t) := rfl

/-- The exact signed effect of one physical swap on any finite labelled line.
    The formula includes both endpoints if both occur in the line. -/
theorem sum_swap_effect {α : Type*} [DecidableEq α] (s : Finset α)
    (f : α → ℤ) (x y : α) (hne : x ≠ y) :
    (∑ z ∈ s, f ((Equiv.swap x y) z)) - (∑ z ∈ s, f z) =
      (if x ∈ s then f y - f x else 0) + (if y ∈ s then f x - f y else 0) := by
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ z ∈ s, (f ((Equiv.swap x y) z) - f z)) =
        ∑ z ∈ s, ((if z = x then f y - f x else 0) +
          (if z = y then f x - f y else 0)) := by
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hx : z = x
      · subst z
        simp [hne]
      · by_cases hy : z = y
        · subst z
          simp [Ne.symm hne]
        · simp [hx, hy, Equiv.swap_apply_of_ne_of_ne hx hy]
    _ = (if x ∈ s then f y - f x else 0) +
        (if y ∈ s then f x - f y else 0) := by
      rw [Finset.sum_add_distrib]
      simp

/-- A line is a finite set of cells; integer coercion retains signed effects
    without natural-number subtraction. -/
def placementLineSum {n : ℕ} (a : Cell n ≃ Fin (n * n)) (s : Finset (Cell n)) : ℤ :=
  ∑ t ∈ s, (entry a t : ℤ)

theorem placementLineSum_swap_effect {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (s : Finset (Cell n)) (x y : Cell n) (hne : x ≠ y) :
    placementLineSum (swapPlacement a x y) s - placementLineSum a s =
      (if x ∈ s then (entry a y : ℤ) - entry a x else 0) +
      (if y ∈ s then (entry a x : ℤ) - entry a y else 0) := by
  simpa [placementLineSum] using
    (sum_swap_effect s (fun t => (entry a t : ℤ)) x y hne)

/-- The RP2 trade swaps both horizontal pairs in their physical cells. -/
def rectangleTrade {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (i j c k : Fin n) : Cell n ≃ Fin (n * n) :=
  swapPlacement (swapPlacement a (i, c) (i, k)) (j, c) (j, k)

/-- Universal line effect for the RP2 trade. No diagonal avoidance is
    assumed: all four possible line contributions appear explicitly. -/
theorem rectangleTrade_line_effect {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (i j c k : Fin n) (h : ℕ) (s : Finset (Cell n))
    (hij : i ≠ j) (hck : c ≠ k)
    (htop : entry a (i, k) = entry a (i, c) + h)
    (hbot : entry a (j, c) = entry a (j, k) + h) :
    placementLineSum (rectangleTrade a i j c k) s - placementLineSum a s =
      (if (i, c) ∈ s then (h : ℤ) else 0) +
      (if (i, k) ∈ s then -(h : ℤ) else 0) +
      (if (j, c) ∈ s then -(h : ℤ) else 0) +
      (if (j, k) ∈ s then (h : ℤ) else 0) := by
  have hxy : (i, c) ≠ (i, k) := by
    intro hpair
    exact hck (congrArg Prod.snd hpair)
  have hzw : (j, c) ≠ (j, k) := by
    intro hpair
    exact hck (congrArg Prod.snd hpair)
  have hzx : (j, c) ≠ (i, c) := by
    intro hpair
    exact hij (congrArg Prod.fst hpair).symm
  have hzy : (j, c) ≠ (i, k) := by
    intro hpair
    exact hij (congrArg Prod.fst hpair).symm
  have hwx : (j, k) ≠ (i, c) := by
    intro hpair
    exact hij (congrArg Prod.fst hpair).symm
  have hwy : (j, k) ≠ (i, k) := by
    intro hpair
    exact hij (congrArg Prod.fst hpair).symm
  have hez : entry (swapPlacement a (i, c) (i, k)) (j, c) = entry a (j, c) := by
    rw [entry_swapPlacement, Equiv.swap_apply_of_ne_of_ne hzx hzy]
  have hew : entry (swapPlacement a (i, c) (i, k)) (j, k) = entry a (j, k) := by
    rw [entry_swapPlacement, Equiv.swap_apply_of_ne_of_ne hwx hwy]
  have htopZ : (entry a (i, k) : ℤ) = (entry a (i, c) : ℤ) + h := by
    exact_mod_cast htop
  have hbotZ : (entry a (j, c) : ℤ) = (entry a (j, k) : ℤ) + h := by
    exact_mod_cast hbot
  have h1 := placementLineSum_swap_effect a s (i, c) (i, k) hxy
  have h2 := placementLineSum_swap_effect (swapPlacement a (i, c) (i, k))
    s (j, c) (j, k) hzw
  rw [hez, hew] at h2
  simp only [htopZ, hbotZ] at h1 h2
  dsimp only [rectangleTrade]
  split_ifs at h1 h2 ⊢ <;> omega

/-- Cell sets for the four kinds of labelled lines. When n=1 they may
    coincide; no distinct-line hypothesis is used. -/
def rowCells {n : ℕ} (i : Fin n) : Finset (Cell n) :=
  Finset.univ.image (fun j => (i, j))

def columnCells {n : ℕ} (j : Fin n) : Finset (Cell n) :=
  Finset.univ.image (fun i => (i, j))

def mainCells (n : ℕ) : Finset (Cell n) :=
  Finset.univ.image (fun i : Fin n => (i, i))

def antiCells (n : ℕ) : Finset (Cell n) :=
  Finset.univ.image (fun i : Fin n => (i, i.rev))

@[simp] theorem mem_rowCells {n : ℕ} (i : Fin n) (z : Cell n) :
    z ∈ rowCells i ↔ z.1 = i := by
  rcases z with ⟨r, c⟩
  simp [rowCells, Prod.ext_iff, eq_comm]

@[simp] theorem mem_columnCells {n : ℕ} (j : Fin n) (z : Cell n) :
    z ∈ columnCells j ↔ z.2 = j := by
  rcases z with ⟨r, c⟩
  simp [columnCells, Prod.ext_iff, eq_comm]

@[simp] theorem mem_mainCells {n : ℕ} (z : Cell n) :
    z ∈ mainCells n ↔ z.1 = z.2 := by
  rcases z with ⟨r, c⟩
  simp [mainCells, Prod.ext_iff]

@[simp] theorem mem_antiCells {n : ℕ} (z : Cell n) :
    z ∈ antiCells n ↔ z.2 = z.1.rev := by
  rcases z with ⟨r, c⟩
  simp [antiCells, Prod.ext_iff, eq_comm]

/-- The finite-set row sum agrees with the public statement's row sum. -/
theorem placementLineSum_row {n : ℕ} (a : Cell n ≃ Fin (n * n)) (i : Fin n) :
    placementLineSum a (rowCells i) = (rowSum a i : ℤ) := by
  unfold placementLineSum rowCells rowSum
  rw [Finset.sum_image (by
    intro x _ y _ h
    exact congrArg Prod.snd h)]
  simp

theorem placementLineSum_column {n : ℕ} (a : Cell n ≃ Fin (n * n)) (j : Fin n) :
    placementLineSum a (columnCells j) = (columnSum a j : ℤ) := by
  unfold placementLineSum columnCells columnSum
  rw [Finset.sum_image (by
    intro x _ y _ h
    exact congrArg Prod.fst h)]
  simp

theorem placementLineSum_main {n : ℕ} (a : Cell n ≃ Fin (n * n)) :
    placementLineSum a (mainCells n) = (mainSum a : ℤ) := by
  unfold placementLineSum mainCells mainSum
  rw [Finset.sum_image (by
    intro x _ y _ h
    exact congrArg Prod.fst h)]
  simp

theorem placementLineSum_anti {n : ℕ} (a : Cell n ≃ Fin (n * n)) :
    placementLineSum a (antiCells n) = (antiSum a : ℤ) := by
  unfold placementLineSum antiCells antiSum
  rw [Finset.sum_image (by
    intro x _ y _ h
    exact congrArg Prod.fst h)]
  simp

/-- With equal, oppositely oriented gaps, every row is preserved. -/
theorem rectangleTrade_rows {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (i j c k : Fin n) (h : ℕ) (hij : i ≠ j) (hck : c ≠ k)
    (htop : entry a (i, k) = entry a (i, c) + h)
    (hbot : entry a (j, c) = entry a (j, k) + h) :
    ∀ r, rowSum (rectangleTrade a i j c k) r = rowSum a r := by
  intro r
  have hline := rectangleTrade_line_effect a i j c k h (rowCells r) hij hck htop hbot
  rw [placementLineSum_row, placementLineSum_row] at hline
  simp only [mem_rowCells] at hline
  split_ifs at hline <;> omega

/-- The opposing gap orientations also preserve every column. -/
theorem rectangleTrade_columns {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (i j c k : Fin n) (h : ℕ) (hij : i ≠ j) (hck : c ≠ k)
    (htop : entry a (i, k) = entry a (i, c) + h)
    (hbot : entry a (j, c) = entry a (j, k) + h) :
    ∀ r, columnSum (rectangleTrade a i j c k) r = columnSum a r := by
  intro r
  have hline := rectangleTrade_line_effect a i j c k h (columnCells r) hij hck htop hbot
  rw [placementLineSum_column, placementLineSum_column] at hline
  simp only [mem_columnCells] at hline
  split_ifs at hline <;> omega

/-- Any line containing exactly the designated corner gains h, while
    a line disjoint from the rectangle is unchanged. -/
theorem rectangleTrade_designated_line {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (i j c k : Fin n) (h : ℕ) (L K : Finset (Cell n))
    (hij : i ≠ j) (hck : c ≠ k)
    (htop : entry a (i, k) = entry a (i, c) + h)
    (hbot : entry a (j, c) = entry a (j, k) + h)
    (hL : (i, c) ∈ L) (hL1 : (i, k) ∉ L) (hL2 : (j, c) ∉ L) (hL3 : (j, k) ∉ L)
    (hK : (i, c) ∉ K) (hK1 : (i, k) ∉ K) (hK2 : (j, c) ∉ K) (hK3 : (j, k) ∉ K) :
    placementLineSum (rectangleTrade a i j c k) L = placementLineSum a L + h ∧
    placementLineSum (rectangleTrade a i j c k) K = placementLineSum a K := by
  have hl := rectangleTrade_line_effect a i j c k h L hij hck htop hbot
  have hk := rectangleTrade_line_effect a i j c k h K hij hck htop hbot
  simp only [hL, hL1, hL2, hL3, hK, hK1, hK2, hK3, if_true, if_false,
    add_zero] at hl hk
  omega

/-- A main-diagonal rectangle changes the main sum by h and preserves the
    full antidiagonal. Its four avoidance hypotheses include the center. -/
theorem rectangleTrade_main {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (i j c k : Fin n) (h : ℕ) (hij : i ≠ j) (hck : c ≠ k)
    (htop : entry a (i, k) = entry a (i, c) + h)
    (hbot : entry a (j, c) = entry a (j, k) + h)
    (hL : (i, c) ∈ mainCells n) (hL1 : (i, k) ∉ mainCells n)
    (hL2 : (j, c) ∉ mainCells n) (hL3 : (j, k) ∉ mainCells n)
    (hK : (i, c) ∉ antiCells n) (hK1 : (i, k) ∉ antiCells n)
    (hK2 : (j, c) ∉ antiCells n) (hK3 : (j, k) ∉ antiCells n) :
    (mainSum (rectangleTrade a i j c k) : ℤ) = (mainSum a : ℤ) + h ∧
    antiSum (rectangleTrade a i j c k) = antiSum a := by
  have hlines := rectangleTrade_designated_line a i j c k h (mainCells n)
    (antiCells n) hij hck htop hbot hL hL1 hL2 hL3 hK hK1 hK2 hK3
  rw [placementLineSum_main, placementLineSum_main,
    placementLineSum_anti, placementLineSum_anti] at hlines
  constructor
  · exact hlines.1
  · exact_mod_cast hlines.2

/-- The same trade can instead repair the antidiagonal while preserving the
    full main diagonal, including its central entry. -/
theorem rectangleTrade_anti {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (i j c k : Fin n) (h : ℕ) (hij : i ≠ j) (hck : c ≠ k)
    (htop : entry a (i, k) = entry a (i, c) + h)
    (hbot : entry a (j, c) = entry a (j, k) + h)
    (hL : (i, c) ∈ antiCells n) (hL1 : (i, k) ∉ antiCells n)
    (hL2 : (j, c) ∉ antiCells n) (hL3 : (j, k) ∉ antiCells n)
    (hK : (i, c) ∉ mainCells n) (hK1 : (i, k) ∉ mainCells n)
    (hK2 : (j, c) ∉ mainCells n) (hK3 : (j, k) ∉ mainCells n) :
    (antiSum (rectangleTrade a i j c k) : ℤ) = (antiSum a : ℤ) + h ∧
    mainSum (rectangleTrade a i j c k) = mainSum a := by
  have hlines := rectangleTrade_designated_line a i j c k h (antiCells n)
    (mainCells n) hij hck htop hbot hL hL1 hL2 hL3 hK hK1 hK2 hK3
  rw [placementLineSum_anti, placementLineSum_anti,
    placementLineSum_main, placementLineSum_main] at hlines
  constructor
  · exact hlines.1
  · exact_mod_cast hlines.2

/-- No cell outside the four physical corners changes. This applies in
    particular to the center whenever it is not one of those corners. -/
theorem rectangleTrade_outside {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (i j c k : Fin n) (t : Cell n)
    (hx : t ≠ (i, c)) (hy : t ≠ (i, k))
    (hz : t ≠ (j, c)) (hw : t ≠ (j, k)) :
    entry (rectangleTrade a i j c k) t = entry a t := by
  simp only [rectangleTrade, entry_swapPlacement]
  rw [Equiv.swap_apply_of_ne_of_ne hz hw, Equiv.swap_apply_of_ne_of_ne hx hy]

/-- Every intermediate and final placement is an actual permutation of the
    exact pool, with no repeated input entry. -/
theorem rectangleTrade_pool_preserved {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (i j c k : Fin n) :
    Set.range (entry (rectangleTrade a i j c k)) = pool n ∧
    Function.Injective (entry (rectangleTrade a i j c k)) :=
  ⟨entry_range _, entry_injective _⟩

/-- Since the top cells are distinct and the pool placement is injective,
    an oriented common gap is necessarily positive. -/
theorem rectangleTrade_gap_positive {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (i c k : Fin n) (h : ℕ) (hck : c ≠ k)
    (htop : entry a (i, k) = entry a (i, c) + h) : 0 < h := by
  by_contra hn
  have hh : h = 0 := by omega
  have he : entry a (i, k) = entry a (i, c) := by simpa [hh] using htop
  have hc : (i, k) = (i, c) := entry_injective a he
  exact hck (congrArg Prod.snd hc).symm

/-- Reverse the two component swaps in reverse order. -/
def undoRectangleTrade {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (i j c k : Fin n) : Cell n ≃ Fin (n * n) :=
  swapPlacement (swapPlacement a (j, c) (j, k)) (i, c) (i, k)

theorem undoRectangleTrade_rectangleTrade {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (i j c k : Fin n) :
    undoRectangleTrade (rectangleTrade a i j c k) i j c k = a := by
  ext t
  simp [undoRectangleTrade, rectangleTrade, swapPlacement]

/-- The middle index of a nonempty square. -/
def centerIndex (n : ℕ) (hn : 0 < n) : Fin n :=
  ⟨n / 2, Nat.div_lt_self hn (by decide)⟩

theorem centerIndex_rev (n : ℕ) (hn : 0 < n) (hodd : Odd n) :
    (centerIndex n hn).rev = centerIndex n hn := by
  apply Fin.ext
  change n - (n / 2 + 1) = n / 2
  obtain ⟨k, hk⟩ := hodd
  omega

/-- The odd-order center is on both labelled diagonals. -/
theorem centerCell_on_both_diagonals (n : ℕ) (hn : 0 < n) (hodd : Odd n) :
    (centerIndex n hn, centerIndex n hn) ∈ mainCells n ∧
    (centerIndex n hn, centerIndex n hn) ∈ antiCells n := by
  simp [centerIndex_rev n hn hodd]

/-- A rectangle avoiding the antidiagonal cannot alter the shared center. -/
theorem rectangleTrade_center_unchanged {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (i j c k : Fin n) (hn : 0 < n) (hodd : Odd n)
    (h1 : (i, c) ∉ antiCells n) (h2 : (i, k) ∉ antiCells n)
    (h3 : (j, c) ∉ antiCells n) (h4 : (j, k) ∉ antiCells n) :
    entry (rectangleTrade a i j c k) (centerIndex n hn, centerIndex n hn) =
      entry a (centerIndex n hn, centerIndex n hn) := by
  have hc := (centerCell_on_both_diagonals n hn hodd).2
  apply rectangleTrade_outside
  · intro heq; exact h1 (heq ▸ hc)
  · intro heq; exact h2 (heq ▸ hc)
  · intro heq; exact h3 (heq ▸ hc)
  · intro heq; exact h4 (heq ▸ hc)

/-- Reversing the physical trade changes the designated main-diagonal
    total back by the same signed amount. -/
theorem undoRectangleTrade_main {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (i j c k : Fin n) (h : ℕ) (hij : i ≠ j) (hck : c ≠ k)
    (htop : entry a (i, k) = entry a (i, c) + h)
    (hbot : entry a (j, c) = entry a (j, k) + h)
    (hL : (i, c) ∈ mainCells n) (hL1 : (i, k) ∉ mainCells n)
    (hL2 : (j, c) ∉ mainCells n) (hL3 : (j, k) ∉ mainCells n)
    (hK : (i, c) ∉ antiCells n) (hK1 : (i, k) ∉ antiCells n)
    (hK2 : (j, c) ∉ antiCells n) (hK3 : (j, k) ∉ antiCells n) :
    (mainSum (undoRectangleTrade (rectangleTrade a i j c k) i j c k) : ℤ) =
      (mainSum (rectangleTrade a i j c k) : ℤ) - h := by
  have hforward := (rectangleTrade_main a i j c k h hij hck htop hbot
    hL hL1 hL2 hL3 hK hK1 hK2 hK3).1
  rw [undoRectangleTrade_rectangleTrade]
  omega

/-- An antidiagonal trade reverses with the same signed correction. -/
theorem undoRectangleTrade_anti {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (i j c k : Fin n) (h : ℕ) (hij : i ≠ j) (hck : c ≠ k)
    (htop : entry a (i, k) = entry a (i, c) + h)
    (hbot : entry a (j, c) = entry a (j, k) + h)
    (hL : (i, c) ∈ antiCells n) (hL1 : (i, k) ∉ antiCells n)
    (hL2 : (j, c) ∉ antiCells n) (hL3 : (j, k) ∉ antiCells n)
    (hK : (i, c) ∉ mainCells n) (hK1 : (i, k) ∉ mainCells n)
    (hK2 : (j, c) ∉ mainCells n) (hK3 : (j, k) ∉ mainCells n) :
    (antiSum (undoRectangleTrade (rectangleTrade a i j c k) i j c k) : ℤ) =
      (antiSum (rectangleTrade a i j c k) : ℤ) - h := by
  have hforward := (rectangleTrade_anti a i j c k h hij hck htop hbot
    hL hL1 hL2 hL3 hK hK1 hK2 hK3).1
  rw [undoRectangleTrade_rectangleTrade]
  omega

/-- A rectangle avoiding the main diagonal also leaves the shared center
    unchanged, as required for an antidiagonal trade. -/
theorem rectangleTrade_center_unchanged_of_main {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (i j c k : Fin n) (hn : 0 < n) (hodd : Odd n)
    (h1 : (i, c) ∉ mainCells n) (h2 : (i, k) ∉ mainCells n)
    (h3 : (j, c) ∉ mainCells n) (h4 : (j, k) ∉ mainCells n) :
    entry (rectangleTrade a i j c k) (centerIndex n hn, centerIndex n hn) =
      entry a (centerIndex n hn, centerIndex n hn) := by
  have hc := (centerCell_on_both_diagonals n hn hodd).1
  apply rectangleTrade_outside
  · intro heq; exact h1 (heq ▸ hc)
  · intro heq; exact h2 (heq ▸ hc)
  · intro heq; exact h3 (heq ▸ hc)
  · intro heq; exact h4 (heq ▸ hc)

end
end Sude
