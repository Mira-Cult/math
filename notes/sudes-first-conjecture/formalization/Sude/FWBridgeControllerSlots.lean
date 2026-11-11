import Sude.FWBridgePlacement
import Sude.BridgeOrdinarySlots

/-! Exact FW bridge endpoint partition into diagonal and ordinary slots. -/
namespace Sude
noncomputable section

/-- The 24 double blocks per stage reserved for the two diagonal families. -/
def fwBridgeDiagonalSlot (n : ℕ) (x : Fin (5 * (4 * 6)) × Fin 4) :
    (Fin 5 × Fin (3 * (n + 8))) × Fin 4 :=
  (bridgeDiagonalBlockSelect (J := 5) (d := 6) (by omega) x.1, x.2)

/-- The remaining 3n double blocks per stage supply one pair to each of
the two ordinary networks. The Boolean pair chooses network and endpoint. -/
def fwBridgeOrdinarySlot (n : ℕ)
    (x : (Fin 5 × (Fin 3 × Fin n)) × (Bool × Bool)) :
    (Fin 5 × Fin (3 * (n + 8))) × Fin 4 :=
  bridgeOrdinarySlot (J := 5) (r := 3) (d := 6) (by omega) x

/-- The two families together address all endpoint slots of the selected
five-stage FW batches. These are slot labels, not physical cells. -/
def fwBridgeControllerSlot (n : ℕ) :
    (Fin (5 * (4 * 6)) × Fin 4) ⊕
      ((Fin 5 × (Fin 3 × Fin n)) × (Bool × Bool)) →
        (Fin 5 × Fin (3 * (n + 8))) × Fin 4 :=
  Sum.elim (fwBridgeDiagonalSlot n) (fwBridgeOrdinarySlot n)

theorem fwBridgeDiagonalSlot_injective (n : ℕ) :
    Function.Injective (fwBridgeDiagonalSlot n) := by
  rintro ⟨x, s⟩ ⟨y, t⟩ h
  have hb := congrArg Prod.fst h
  have hs := congrArg Prod.snd h
  have hxy : x = y := bridgeDiagonalBlockSelect_injective (J := 5) (d := 6) (by omega) hb
  cases hxy
  cases hs
  rfl

theorem fwBridgeOrdinarySlot_injective (n : ℕ) :
    Function.Injective (fwBridgeOrdinarySlot n) :=
  bridgeOrdinarySlot_injective (J := 5) (r := 3) (d := 6) (by omega)

/-- The source's diagonal and ordinary slot families are disjoint and
exhaust the exact endpoint population, with no discarded block. -/
theorem fwBridgeControllerSlot_bijective (n : ℕ) :
    Function.Bijective (fwBridgeControllerSlot n) := by
  have hinj : Function.Injective (fwBridgeControllerSlot n) := by
    intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        exact congrArg Sum.inl (fwBridgeDiagonalSlot_injective n h)
      | inr y =>
        exfalso
        exact bridgeOrdinarySlot_ne_diagonal (J := 5) (r := 3) (d := 6)
          (by omega) (by omega) y x.1 x.2 h.symm
    | inr x =>
      cases y with
      | inl y =>
        exfalso
        exact bridgeOrdinarySlot_ne_diagonal (J := 5) (r := 3) (d := 6)
          (by omega) (by omega) x y.1 y.2 h
      | inr y =>
        exact congrArg Sum.inr (fwBridgeOrdinarySlot_injective n h)
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨hinj, ?_⟩
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  omega

/-- Reindexing by the source slot split preserves distinctness of actual
FW pool entries. This does not place them in physical rectangles or layers. -/
theorem fwBridgeControllerEndpoint_injective (n : ℕ) (initial : Finset ℕ)
    (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n initial batches j) :
    Function.Injective (fun x =>
      fwBridgeStageEndpoint n initial batches hvalid (fwBridgeControllerSlot n x)) := by
  exact (fwBridgeStageEndpoint_injective n initial batches hvalid).comp
    (fwBridgeControllerSlot_bijective n).1

end
end Sude
