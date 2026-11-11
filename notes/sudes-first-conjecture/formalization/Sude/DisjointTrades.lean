import Sude.Switches
import Mathlib.GroupTheory.Perm.Support

/-! Disjoint physical rectangle supports. No packing existence is assumed. -/
namespace Sude
noncomputable section

/-- The four actual cells occupied by a rectangle. -/
def rectangleCells {n : ℕ} (i j c k : Fin n) : Finset (Cell n) :=
  {(i, c), (i, k), (j, c), (j, k)}

@[simp] theorem mem_rectangleCells {n : ℕ} (i j c k : Fin n) (t : Cell n) :
    t ∈ rectangleCells i j c k ↔
      t = (i, c) ∨ t = (i, k) ∨ t = (j, c) ∨ t = (j, k) := by
  simp [rectangleCells]

/-- Disjoint rectangles retain each other's actual values, not merely their
    abstract row or column balances. -/
theorem rectangleTrade_other_cells_unchanged {n : ℕ}
    (a : Cell n ≃ Fin (n * n)) (i j c k i' j' c' k' : Fin n)
    (hdisj : Disjoint (rectangleCells i j c k) (rectangleCells i' j' c' k')) :
    ∀ t ∈ rectangleCells i' j' c' k',
      entry (rectangleTrade a i j c k) t = entry a t := by
  intro t ht
  have hn : t ∉ rectangleCells i j c k := by
    intro hm
    exact Finset.disjoint_left.mp hdisj hm ht
  rw [mem_rectangleCells] at hn
  simp only [not_or] at hn
  exact rectangleTrade_outside a i j c k t hn.1 hn.2.1 hn.2.2.1 hn.2.2.2

/-- In particular, both equal-gap pair hypotheses of a disjoint later
    rectangle remain true after the first physical trade. -/
theorem rectangleTrade_other_gaps_unchanged {n : ℕ}
    (a : Cell n ≃ Fin (n * n)) (i j c k i' j' c' k' : Fin n) (h : ℕ)
    (hdisj : Disjoint (rectangleCells i j c k) (rectangleCells i' j' c' k'))
    (htop : entry a (i', k') = entry a (i', c') + h)
    (hbot : entry a (j', c') = entry a (j', k') + h) :
    entry (rectangleTrade a i j c k) (i', k') =
        entry (rectangleTrade a i j c k) (i', c') + h ∧
      entry (rectangleTrade a i j c k) (j', c') =
        entry (rectangleTrade a i j c k) (j', k') + h := by
  have hfix := rectangleTrade_other_cells_unchanged a i j c k i' j' c' k' hdisj
  have h1 := hfix (i', k') (by simp)
  have h2 := hfix (i', c') (by simp)
  have h3 := hfix (j', c') (by simp)
  have h4 := hfix (j', k') (by simp)
  rw [h1, h2, h3, h4]
  exact ⟨htop, hbot⟩

/-- A trade's cell permutation, prior to applying the value placement. -/
def rectanglePerm {n : ℕ} (i j c k : Fin n) : Equiv.Perm (Cell n) :=
  (Equiv.swap (j, c) (j, k)).trans (Equiv.swap (i, c) (i, k))

theorem rectanglePerm_fixes_outside {n : ℕ} (i j c k : Fin n) (t : Cell n)
    (ht : t ∉ rectangleCells i j c k) : rectanglePerm i j c k t = t := by
  rw [mem_rectangleCells] at ht
  simp only [not_or] at ht
  simp only [rectanglePerm, Equiv.trans_apply]
  rw [Equiv.swap_apply_of_ne_of_ne ht.2.2.1 ht.2.2.2,
    Equiv.swap_apply_of_ne_of_ne ht.1 ht.2.1]

theorem rectanglePerm_disjoint {n : ℕ} (i j c k i' j' c' k' : Fin n)
    (hdisj : Disjoint (rectangleCells i j c k) (rectangleCells i' j' c' k')) :
    Equiv.Perm.Disjoint (rectanglePerm i j c k) (rectanglePerm i' j' c' k') := by
  intro t
  by_cases ht : t ∈ rectangleCells i j c k
  · right
    apply rectanglePerm_fixes_outside
    intro ht'
    exact Finset.disjoint_left.mp hdisj ht ht'
  · left
    exact rectanglePerm_fixes_outside i j c k t ht

/-- Disjoint physical trades commute as permutations of the actual input. -/
theorem rectangleTrade_commute_disjoint {n : ℕ}
    (a : Cell n ≃ Fin (n * n)) (i j c k i' j' c' k' : Fin n)
    (hdisj : Disjoint (rectangleCells i j c k) (rectangleCells i' j' c' k')) :
    rectangleTrade (rectangleTrade a i j c k) i' j' c' k' =
      rectangleTrade (rectangleTrade a i' j' c' k') i j c k := by
  have hc := (rectanglePerm_disjoint i j c k i' j' c' k' hdisj).commute.eq
  ext t
  have ht := congrArg (fun p : Equiv.Perm (Cell n) => p t) hc
  simp only [Equiv.Perm.mul_apply, rectanglePerm, Equiv.trans_apply] at ht
  simp only [rectangleTrade, swapPlacement, Equiv.trans_apply]
  exact congrArg (fun z => (a z).val) ht

/-- Two disjoint physical rectangles can repair the main and antidiagonal
    in sequence. The second uses the same actual entries after the first. -/
theorem rectangleTrade_main_then_anti {n : ℕ}
    (a : Cell n ≃ Fin (n * n)) (i j c k i' j' c' k' : Fin n)
    (h h' : ℕ)
    (hdisj : Disjoint (rectangleCells i j c k) (rectangleCells i' j' c' k'))
    (hij : i ≠ j) (hck : c ≠ k) (hij' : i' ≠ j') (hck' : c' ≠ k')
    (htop : entry a (i, k) = entry a (i, c) + h)
    (hbot : entry a (j, c) = entry a (j, k) + h)
    (htop' : entry a (i', k') = entry a (i', c') + h')
    (hbot' : entry a (j', c') = entry a (j', k') + h')
    (m1 : (i, c) ∈ mainCells n) (m2 : (i, k) ∉ mainCells n)
    (m3 : (j, c) ∉ mainCells n) (m4 : (j, k) ∉ mainCells n)
    (a1 : (i, c) ∉ antiCells n) (a2 : (i, k) ∉ antiCells n)
    (a3 : (j, c) ∉ antiCells n) (a4 : (j, k) ∉ antiCells n)
    (a1' : (i', c') ∈ antiCells n) (a2' : (i', k') ∉ antiCells n)
    (a3' : (j', c') ∉ antiCells n) (a4' : (j', k') ∉ antiCells n)
    (m1' : (i', c') ∉ mainCells n) (m2' : (i', k') ∉ mainCells n)
    (m3' : (j', c') ∉ mainCells n) (m4' : (j', k') ∉ mainCells n) :
    let result := rectangleTrade (rectangleTrade a i j c k) i' j' c' k'
    (∀ r, rowSum result r = rowSum a r) ∧
    (∀ r, columnSum result r = columnSum a r) ∧
    (mainSum result : ℤ) = (mainSum a : ℤ) + h ∧
    (antiSum result : ℤ) = (antiSum a : ℤ) + h' ∧
    Set.range (entry result) = pool n ∧ Function.Injective (entry result) := by
  dsimp only
  have hg := rectangleTrade_other_gaps_unchanged a i j c k i' j' c' k' h'
    hdisj htop' hbot'
  have hr1 := rectangleTrade_rows a i j c k h hij hck htop hbot
  have hc1 := rectangleTrade_columns a i j c k h hij hck htop hbot
  have hr2 := rectangleTrade_rows (rectangleTrade a i j c k) i' j' c' k' h'
    hij' hck' hg.1 hg.2
  have hc2 := rectangleTrade_columns (rectangleTrade a i j c k) i' j' c' k' h'
    hij' hck' hg.1 hg.2
  have hm := rectangleTrade_main a i j c k h hij hck htop hbot
    m1 m2 m3 m4 a1 a2 a3 a4
  have ha := rectangleTrade_anti (rectangleTrade a i j c k) i' j' c' k' h'
    hij' hck' hg.1 hg.2 a1' a2' a3' a4' m1' m2' m3' m4'
  refine ⟨?_, ?_, ?_, ?_, entry_range _, entry_injective _⟩
  · intro r
    exact (hr2 r).trans (hr1 r)
  · intro r
    exact (hc2 r).trans (hc1 r)
  · rw [ha.2]
    exact hm.1
  · rw [hm.2] at ha
    exact ha.1

/-- The two opposite-diagonal trades retain the shared central entry.
    This follows directly from their physical supports. -/
theorem rectangleTrade_main_then_anti_center {n : ℕ}
    (a : Cell n ≃ Fin (n * n)) (i j c k i' j' c' k' : Fin n)
    (hn : 0 < n) (hodd : Odd n)
    (a1 : (i, c) ∉ antiCells n) (a2 : (i, k) ∉ antiCells n)
    (a3 : (j, c) ∉ antiCells n) (a4 : (j, k) ∉ antiCells n)
    (m1 : (i', c') ∉ mainCells n) (m2 : (i', k') ∉ mainCells n)
    (m3 : (j', c') ∉ mainCells n) (m4 : (j', k') ∉ mainCells n) :
    entry (rectangleTrade (rectangleTrade a i j c k) i' j' c' k')
        (centerIndex n hn, centerIndex n hn) =
      entry a (centerIndex n hn, centerIndex n hn) := by
  have h1 := rectangleTrade_center_unchanged a i j c k hn hodd a1 a2 a3 a4
  have h2 := rectangleTrade_center_unchanged_of_main (rectangleTrade a i j c k)
    i' j' c' k' hn hodd m1 m2 m3 m4
  exact h2.trans h1

end
end Sude
