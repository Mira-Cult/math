import Sude.FWSeedOffsetDiagonalInvoice
import Sude.DiagonalPhysicalInvoice

/-! Lift the offset seed diagonal rectangle invoice to pair slots. Ordinary
network tags have zero modeled weight; identification with actual cells
requires the separate packed-layer off-diagonal argument. -/
namespace Sude
noncomputable section

noncomputable def fwSeedOffsetDiagonalIncidence {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (line : Cell n → Prop) (j : Fin 16) : PrefixStagePair 6 3 n → ℝ
  | Sum.inl (rect, pair) => rectanglePairWeight hs choice line
      (fwSeedRectangle hseed (finProdFinEquiv (j, rect)), pair)
  | Sum.inr _ => 0

theorem fw_seed_offset_diagonal_incidence_nonneg {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (line : Cell n → Prop) (j : Fin 16) (x : PrefixStagePair 6 3 n) :
    0 ≤ fwSeedOffsetDiagonalIncidence hseed hs choice line j x := by
  cases x with
  | inl x =>
    rcases x with ⟨rect, pair⟩
    exact rectanglePairWeight_nonneg hs choice line _
  | inr x => norm_num [fwSeedOffsetDiagonalIncidence]

theorem fw_seed_offset_diagonal_incidence_sq_sum {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (line : Cell n → Prop) (j : Fin 16) :
    (∑ x, (fwSeedOffsetDiagonalIncidence hseed hs choice line j x) ^ 2) =
      fwSeedOffsetRectangleStageInvoice hseed hs choice line j := by
  simp [fwSeedOffsetDiagonalIncidence, fwSeedOffsetRectangleStageInvoice,
    Fintype.sum_sum_type, Fintype.sum_prod_type]

/-- The diagonal weights lifted to the actual stage pair-slot indices. -/
noncomputable def fwSeedOffsetDiagonalSlotWeight {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (line : Cell n → Prop) (j : Fin 16) :
    Fin (6 * (n + 8)) → ℝ :=
  liftedSlotWeight (prefixStagePairSlot
      (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
      (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega))
    (fwSeedOffsetDiagonalIncidence hseed hs choice line j)

theorem fw_seed_offset_diagonal_slot_weight_nonneg {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (line : Cell n → Prop) (j : Fin 16) (q : Fin (6 * (n + 8))) :
    0 ≤ fwSeedOffsetDiagonalSlotWeight hseed hs choice line j q :=
  liftedSlotWeight_nonneg _ _ (fw_seed_offset_diagonal_incidence_nonneg hseed hs choice line j) q

theorem fw_seed_offset_diagonal_slot_sq_sum {n L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (line : Cell n → Prop) (j : Fin 16) :
    (∑ q ∈ physicalPrefixSlots
      (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
      (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega),
      (fwSeedOffsetDiagonalSlotWeight hseed hs choice line j q) ^ 2) =
      fwSeedOffsetRectangleStageInvoice hseed hs choice line j := by
  rw [show (∑ q ∈ physicalPrefixSlots
      (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
      (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega),
      (fwSeedOffsetDiagonalSlotWeight hseed hs choice line j q) ^ 2) =
      ∑ x, (fwSeedOffsetDiagonalIncidence hseed hs choice line j x) ^ 2 from
    liftedSlotWeight_sq_sum _ (prefixStagePairSlot_injective _ _) _]
  exact fw_seed_offset_diagonal_incidence_sq_sum hseed hs choice line j

/-- The main-diagonal width-weighted slot invoice is exactly twelve times
the sum of squared supplied widths. -/
theorem fw_seed_offset_main_weighted_invoice {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (otherChoice : Fin L → Bool) (width : Fin 16 → ℝ) :
    (∑ j, (width j) ^ 2 * ∑ q ∈ physicalPrefixSlots
      (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
      (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega),
      (fwSeedOffsetDiagonalSlotWeight hseed hs (fwBridgeSeedRectangleChoice hrect hseed otherChoice)
        (fun c => c ∈ mainCells n) j q) ^ 2) = 12 * ∑ j, (width j) ^ 2 := by
  simp_rw [fw_seed_offset_diagonal_slot_sq_sum,
    fw_seed_offset_main_stage_invoice hrect hseed hs hL otherChoice]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The corresponding antidiagonal width-weighted slot invoice. -/
theorem fw_seed_offset_anti_weighted_invoice {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (otherChoice : Fin L → Bool) (width : Fin 16 → ℝ) :
    (∑ j, (width j) ^ 2 * ∑ q ∈ physicalPrefixSlots
      (show (4 * 6) * 2 + 2 * (3 * n) ≤ 6 * (n + 8) by omega)
      (show (4 * 6) * 2 ≤ 6 * (n + 8) by omega),
      (fwSeedOffsetDiagonalSlotWeight hseed hs (fwBridgeSeedRectangleChoice hrect hseed otherChoice)
        (fun c => c ∈ antiCells n) j q) ^ 2) = 12 * ∑ j, (width j) ^ 2 := by
  simp_rw [fw_seed_offset_diagonal_slot_sq_sum,
    fw_seed_offset_anti_stage_invoice hrect hseed hs hL otherChoice]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end
end Sude
