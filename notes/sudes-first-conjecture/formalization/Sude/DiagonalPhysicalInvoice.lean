import Sude.DiagonalStageInvoice
import Sude.PhysicalSlotNonnegative
import Sude.LayerTranspose

/-! Physical diagonal slot weights, including network avoidance. -/
namespace Sude
noncomputable section

/-- Every actual packed stage-network cell avoids both labelled diagonals. -/
theorem prefixStageLayer_off_diagonals {P layers n : ℕ}
    (network : List (LayerPacking.Layer n)) (hlen : network.length = P * layers)
    (reserved : Finset (Cell n)) (packed : LayerPacking.PackedLayers reserved network)
    (j : Fin P) (k : Fin layers) (edge : Fin n) (side : Bool) :
    LayerPacking.layerCell (prefixStageLayer network hlen j k).1
      (prefixStageLayer network hlen j k).2 (edge, side) ∉ mainCells n ∧
    LayerPacking.layerCell (prefixStageLayer network hlen j k).1
      (prefixStageLayer network hlen j k).2 (edge, side) ∉ antiCells n := by
  let idx : Fin network.length := Fin.cast hlen.symm (finProdFinEquiv (j, k))
  have hm := LayerPacking.sequenceCell_mem network idx (edge, side)
  have hs := (packed.each_layer (network.get idx) (List.get_mem _ _)).2.1 _ hm
  exact ⟨hs.2.1, hs.2.2⟩

/-- Transposed physical network cells also avoid both diagonals. -/
theorem prefixStageLayer_swap_off_diagonals {P layers n : ℕ}
    (network : List (LayerPacking.Layer n)) (hlen : network.length = P * layers)
    (reserved : Finset (Cell n)) (packed : LayerPacking.PackedLayers reserved network)
    (j : Fin P) (k : Fin layers) (edge : Fin n) (side : Bool) :
    (LayerPacking.layerCell (prefixStageLayer network hlen j k).1
      (prefixStageLayer network hlen j k).2 (edge, side)).swap ∉ mainCells n ∧
    (LayerPacking.layerCell (prefixStageLayer network hlen j k).1
      (prefixStageLayer network hlen j k).2 (edge, side)).swap ∉ antiCells n := by
  have h := prefixStageLayer_off_diagonals network hlen reserved packed j k edge side
  constructor
  · intro hz
    exact h.1 ((LayerPacking.swap_mem_main _).mp hz)
  · intro hz
    exact h.2 ((LayerPacking.swap_mem_anti _).mp hz)

/-- The physical diagonal weight of a stage pair: ordinary networks have
zero incidence because their actual cells avoid both diagonals. -/
noncomputable def prefixStageDiagonalIncidence {P d layers n L : ℕ}
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (line : Cell n → Prop) (j : Fin P) : PrefixStagePair d layers n → ℝ
  | Sum.inl (rect, pair) => rectanglePairWeight hs choice line (prefixRectanglePairSlot hrect ((j, rect), pair))
  | Sum.inr _ => 0

/-- The diagonal slot weights are nonnegative. -/
theorem prefixStageDiagonalIncidence_nonneg {P d layers n L : ℕ}
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (line : Cell n → Prop) (j : Fin P) (x : PrefixStagePair d layers n) :
    0 ≤ prefixStageDiagonalIncidence hrect hs choice line j x := by
  cases x with
  | inl x =>
    rcases x with ⟨rect, pair⟩
    change 0 ≤ rectanglePairWeight hs choice line (prefixRectanglePairSlot hrect ((j, rect), pair))
    exact rectanglePairWeight_nonneg hs choice line _
  | inr x => norm_num [prefixStageDiagonalIncidence]

/-- Diagonal label squares are precisely the rectangle stage invoice. -/
theorem prefixStageDiagonalIncidence_sq_sum {P d layers n L : ℕ}
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (line : Cell n → Prop) (j : Fin P) :
    (∑ x, (prefixStageDiagonalIncidence (layers := layers) (n := n) hrect hs choice line j x) ^ 2) =
      prefixRectangleStageInvoice hrect hs choice line j := by
  simp [prefixStageDiagonalIncidence, prefixRectangleStageInvoice, Fintype.sum_sum_type,
    Fintype.sum_prod_type]

/-- The actual diagonal incidence weights on allocator slots. -/
noncomputable def physicalDiagonalSlotWeight {P d layers n L Q : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (line : Cell n → Prop) (j : Fin P) : Fin Q → ℝ :=
  liftedSlotWeight (prefixStagePairSlot hfit hdiag)
    (prefixStageDiagonalIncidence hrect hs choice line j)

theorem physicalDiagonalSlotWeight_nonneg {P d layers n L Q : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (line : Cell n → Prop) (j : Fin P) (q : Fin Q) :
    0 ≤ physicalDiagonalSlotWeight hfit hdiag hrect hs choice line j q :=
  liftedSlotWeight_nonneg _ _ (prefixStageDiagonalIncidence_nonneg hrect hs choice line j) q

/-- Diagonal squared weights in actual slot coordinates equal the rectangle
invoice; the injective map proves there is no slot collision. -/
theorem physicalDiagonalSlotWeight_sq_sum {P d layers n L Q : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hdiag : (4 * d) * 2 ≤ Q)
    (hrect : P * (4 * d) ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (line : Cell n → Prop) (j : Fin P) :
    (∑ q ∈ physicalPrefixSlots hfit hdiag,
      (physicalDiagonalSlotWeight hfit hdiag hrect hs choice line j q) ^ 2) =
      prefixRectangleStageInvoice hrect hs choice line j := by
  rw [show (∑ q ∈ physicalPrefixSlots hfit hdiag,
      (physicalDiagonalSlotWeight hfit hdiag hrect hs choice line j q) ^ 2) =
      ∑ x, (prefixStageDiagonalIncidence hrect hs choice line j x) ^ 2 from
    liftedSlotWeight_sq_sum _ (prefixStagePairSlot_injective hfit hdiag) _]
  exact prefixStageDiagonalIncidence_sq_sum hrect hs choice line j

end
end Sude
