import Sude.RectangleLineCardinality
import Sude.NarrowPoolValues

/-! Convert actual rectangle corner counts into pair-slot incidence weights. -/
namespace Sude
noncomputable section

/-- Each rectangle's two pair labels and endpoint orientations enumerate its
four corners, including the reversed orientation of the second pair. -/
def rectanglePairCornerEquiv (L : ℕ) : ((Fin L × Fin 2) × Bool) ≃ (Fin L × Fin 4) where
  toFun x := (x.1.1, prefixPairCorner x.1.2 x.2)
  invFun x := ((x.1, (prefixCornerCode x.2).1), (prefixCornerCode x.2).2)
  left_inv := by
    rintro ⟨⟨j, p⟩, b⟩
    fin_cases p <;> cases b <;> rfl
  right_inv := by
    rintro ⟨j, c⟩
    fin_cases c <;> rfl

/-- The number of this rectangle pair's endpoints lying on a labelled line. -/
noncomputable def rectanglePairWeight {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (line : Cell n → Prop) (p : Fin L × Fin 2) : ℝ := by
  classical
  exact (if line (packedRectangleCorner hs choice (p.1, prefixPairCorner p.2 false)) then 1 else 0) +
    (if line (packedRectangleCorner hs choice (p.1, prefixPairCorner p.2 true)) then 1 else 0)

/-- Total pair weight counts actual physical endpoints, not abstract slots. -/
theorem rectanglePairWeight_sum_eq_card {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (line : Cell n → Prop) [DecidablePred line] :
    (∑ p, rectanglePairWeight hs choice line p) =
      (((Finset.univ : Finset (Fin L × Fin 4)).filter
        (fun x => line (packedRectangleCorner hs choice x))).card : ℝ) := by
  classical
  let e := rectanglePairCornerEquiv L
  calc
    (∑ p, rectanglePairWeight hs choice line p) =
        ∑ x : ((Fin L × Fin 2) × Bool),
          if line (packedRectangleCorner hs choice (e x)) then (1 : ℝ) else 0 := by
      rw [Fintype.sum_prod_type (fun x : ((Fin L × Fin 2) × Bool) =>
        if line (packedRectangleCorner hs choice (e x)) then (1 : ℝ) else 0)]
      apply Finset.sum_congr rfl
      intro p _
      rw [Fintype.sum_bool]
      simp [rectanglePairWeight, e, rectanglePairCornerEquiv, add_comm] <;>
        split_ifs <;> norm_num
    _ = ∑ y : Fin L × Fin 4,
          if line (packedRectangleCorner hs choice y) then (1 : ℝ) else 0 :=
      e.sum_comp (fun y : Fin L × Fin 4 =>
        if line (packedRectangleCorner hs choice y) then (1 : ℝ) else 0)
    _ = _ := by simp

/-- All packed rectangle pairs together contribute at most four to a row's
squared endpoint-incidence weight invoice. -/
theorem packedRectangle_row_pair_invoice {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (r : Fin n) :
    (∑ p, (rectanglePairWeight hs choice (fun c => c.1 = r) p) ^ 2) ≤ 4 := by
  classical
  let w := rectanglePairWeight hs choice (fun c => c.1 = r)
  have hn : ∀ p ∈ (Finset.univ : Finset (Fin L × Fin 2)), 0 ≤ w p := by
    intro p _
    dsimp [w, rectanglePairWeight]
    split_ifs <;> norm_num
  have hsum : (∑ p, w p) ≤ 2 := by
    rw [rectanglePairWeight_sum_eq_card]
    exact_mod_cast packedRectangle_row_card_le_two hs choice r
  exact squared_incidence_le_four Finset.univ w hn (by simpa using hsum)

/-- The same squared-weight bound holds for every column. -/
theorem packedRectangle_column_pair_invoice {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (c : Fin n) :
    (∑ p, (rectanglePairWeight hs choice (fun x => x.2 = c) p) ^ 2) ≤ 4 := by
  classical
  let w := rectanglePairWeight hs choice (fun x => x.2 = c)
  have hn : ∀ p ∈ (Finset.univ : Finset (Fin L × Fin 2)), 0 ≤ w p := by
    intro p _
    dsimp [w, rectanglePairWeight]
    split_ifs <;> norm_num
  have hsum : (∑ p, w p) ≤ 2 := by
    rw [rectanglePairWeight_sum_eq_card]
    exact_mod_cast packedRectangle_column_card_le_two hs choice c
  exact squared_incidence_le_four Finset.univ w hn (by simpa using hsum)

end
end Sude
