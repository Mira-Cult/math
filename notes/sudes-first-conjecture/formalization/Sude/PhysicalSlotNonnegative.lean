import Sude.PhysicalSlotInvoice

/-! Actual physical incidence weights are nonnegative. -/
namespace Sude
noncomputable section

theorem rectanglePairWeight_nonneg {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (line : Cell n → Prop) (p : Fin L × Fin 2) :
    0 ≤ rectanglePairWeight hs choice line p := by
  classical
  unfold rectanglePairWeight
  split_ifs <;> norm_num

theorem LayerPacking.layerRowWeight_nonneg {n : ℕ} (π f : Equiv.Perm (Fin n))
    (r i : Fin n) : 0 ≤ LayerPacking.layerRowWeight π f r i := by
  unfold LayerPacking.layerRowWeight
  split_ifs <;> norm_num

theorem LayerPacking.layerColumnWeight_nonneg {n : ℕ} (π f : Equiv.Perm (Fin n))
    (c i : Fin n) : 0 ≤ LayerPacking.layerColumnWeight π f c i := by
  unfold LayerPacking.layerColumnWeight
  split_ifs <;> norm_num

theorem prefixStageRowIncidence_nonneg {P d layers n L : ℕ}
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (j : Fin P) (r : Fin n)
    (x : PrefixStagePair d layers n) :
    0 ≤ prefixStageRowIncidence hrect hs choice rows cols hrows hcols j r x := by
  cases x with
  | inl x =>
    rcases x with ⟨rect, pair⟩
    change 0 ≤ rectanglePairWeight hs choice (fun c => c.1 = r)
      (prefixRectanglePairSlot hrect ((j, rect), pair))
    exact rectanglePairWeight_nonneg hs choice _ _
  | inr x =>
    rcases x with ⟨network, layer, edge⟩
    simp only [prefixStageRowIncidence]
    split
    · exact LayerPacking.layerRowWeight_nonneg _ _ _ _
    · exact LayerPacking.layerColumnWeight_nonneg _ _ _ _

theorem prefixStageColumnIncidence_nonneg {P d layers n L : ℕ}
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (j : Fin P) (c : Fin n)
    (x : PrefixStagePair d layers n) :
    0 ≤ prefixStageColumnIncidence hrect hs choice rows cols hrows hcols j c x := by
  cases x with
  | inl x =>
    rcases x with ⟨rect, pair⟩
    change 0 ≤ rectanglePairWeight hs choice (fun x => x.2 = c)
      (prefixRectanglePairSlot hrect ((j, rect), pair))
    exact rectanglePairWeight_nonneg hs choice _ _
  | inr x =>
    rcases x with ⟨network, layer, edge⟩
    simp only [prefixStageColumnIncidence]
    split
    · exact LayerPacking.layerColumnWeight_nonneg _ _ _ _
    · exact LayerPacking.layerRowWeight_nonneg _ _ _ _

/-- Extending nonnegative label weights by zero keeps all slot weights nonnegative. -/
theorem liftedSlotWeight_nonneg {α β : Type*} [Fintype α] [DecidableEq β]
    (slot : α → β) (weight : α → ℝ) (hweight : ∀ x, 0 ≤ weight x) (q : β) :
    0 ≤ liftedSlotWeight slot weight q := by
  classical
  unfold liftedSlotWeight
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact hweight x
  · exact le_rfl

theorem physicalRowSlotWeight_nonneg {P d layers n L Q : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (j : Fin P) (r : Fin n) (q : Fin Q) :
    0 ≤ physicalRowSlotWeight hfit hdiag hrect hs choice rows cols hrows hcols j r q :=
  liftedSlotWeight_nonneg _ _ (prefixStageRowIncidence_nonneg hrect hs choice rows cols hrows hcols j r) q

theorem physicalColumnSlotWeight_nonneg {P d layers n L Q : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hrows : rows.length = P * layers)
    (hcols : cols.length = P * layers) (j : Fin P) (c : Fin n) (q : Fin Q) :
    0 ≤ physicalColumnSlotWeight hfit hdiag hrect hs choice rows cols hrows hcols j c q :=
  liftedSlotWeight_nonneg _ _ (prefixStageColumnIncidence_nonneg hrect hs choice rows cols hrows hcols j c) q

end
end Sude
