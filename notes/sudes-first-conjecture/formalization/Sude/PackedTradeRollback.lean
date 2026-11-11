import Sude.PackedTradeSequence

/-! Reversing physical packed-trade sequences. This records a permutation
identity, without supplying diagonal grids or prime targets. -/
namespace Sude
noncomputable section

/-- A sequence applies the first list and then the second. -/
theorem packedTradeSequence_append {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (a : Cell n ≃ Fin (n*n)) (xs ys : List (Fin L)) :
    packedTradeSequence hs choice a (xs ++ ys) =
      packedTradeSequence hs choice (packedTradeSequence hs choice a xs) ys := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, packedTradeSequence]
    exact ih _

/-- One packed rectangle trade is an involution on the actual placement. -/
theorem packedTrade_involutive {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (a : Cell n ≃ Fin (n*n)) (i : Fin L) :
    packedTrade hs choice (packedTrade hs choice a i) i = a := by
  let r := RectanglePacking.firstRow hs i
  let s := RectanglePacking.secondRow hs i
  let c := RectanglePacking.firstColumn hs choice i
  let d := RectanglePacking.secondColumn hs choice i
  have hrs : r ≠ s := RectanglePacking.firstRow_ne_secondRow hs i i
  have hcd : c ≠ d := RectanglePacking.firstColumn_ne_secondColumn hs choice i i
  change rectangleTrade (rectangleTrade a r s c d) r s c d = a
  ext x
  simp only [rectangleTrade, swapPlacement, Equiv.trans_apply, Equiv.swap_apply_def]
  split_ifs <;> simp_all [Prod.mk.injEq, Ne.symm hrs, Ne.symm hcd]

/-- Reversing any sequence rolls back every physical packed trade. No
noduplication, equal-gap or ordering hypothesis is needed for this identity. -/
theorem packedTradeSequence_reverse {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (a : Cell n ≃ Fin (n*n)) (xs : List (Fin L)) :
    packedTradeSequence hs choice (packedTradeSequence hs choice a xs) xs.reverse = a := by
  induction xs generalizing a with
  | nil => rfl
  | cons i rest ih =>
    simp only [packedTradeSequence, List.reverse_cons]
    rw [packedTradeSequence_append]
    change packedTrade hs choice
      (packedTradeSequence hs choice (packedTradeSequence hs choice (packedTrade hs choice a i) rest)
        rest.reverse) i = a
    rw [ih]
    exact packedTrade_involutive hs choice a i

end
end Sude
