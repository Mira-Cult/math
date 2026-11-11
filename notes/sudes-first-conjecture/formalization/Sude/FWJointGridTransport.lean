import Sude.BridgePhysicalGrid
import Sude.FWJointPhysicalGaps

/-! Transfer one supported even grid to two actual joint-layer pair systems.
Label maps, their injectivity, and physical gap identities are supplied. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096

/-- The pre-wide support and the finite family of fresh wide-stage labels. -/
def fwJointGridLabels {α : Type*} [DecidableEq α] (base : Finset α) (J : ℕ) :
    Finset (Sum α (Fin J)) :=
  base.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
    (Finset.univ : Finset (Fin J)).map ⟨Sum.inr, Sum.inr_injective⟩

/-- Transport row and column grids with the same supported labels and chosen
wide-gap function to actual layer slots of one supplied square. Only the
supported labels need be injected. This does not prove cross-edge reservoir
disjointness, flow, placement, or the supplied physical gap identities. -/
theorem fw_joint_row_column_grid_transport {α : Type*} [DecidableEq α] {n J : ℕ}
    (a : Cell n ≃ Fin (n * n)) (rows cols : List (LayerPacking.Layer n))
    (p : Fin 3 → Equiv.Perm (Fin n)) (edge : Fin 3 × Fin n)
    (base : Finset α) (rowBaseGap colBaseGap : α → ℕ) (wide : Fin J → ℕ) (R : ℕ)
    (hrowgrid : CompleteEvenGrid (fwJointGridLabels base J) (Sum.elim rowBaseGap wide) R)
    (hcolgrid : CompleteEvenGrid (fwJointGridLabels base J) (Sum.elim colBaseGap wide) R)
    (rowSlot : {x // x ∈ fwJointGridLabels base J} → Fin rows.length × Fin n)
    (colSlot : {x // x ∈ fwJointGridLabels base J} → Fin cols.length × Fin n)
    (hrowinj : Function.Injective rowSlot) (hcolinj : Function.Injective colSlot)
    (hrowgap : ∀ x, fwPhysicalRowLayerGap a rows (rowSlot x).1 (rowSlot x).2 =
      Sum.elim rowBaseGap wide x.val)
    (hcolgap : ∀ x, fwPhysicalColumnLayerGap a cols (colSlot x).1 (colSlot x).2 =
      Sum.elim colBaseGap wide x.val)
    (hrowedge : ∀ x, (rowSlot x).2 = edge.2 ∧
      (rows.get (rowSlot x).1).1 edge.2 = p edge.1 edge.2)
    (hcoledge : ∀ x, (colSlot x).2 = edge.2 ∧
      (cols.get (colSlot x).1).1 edge.2 = p edge.1 edge.2) :
    CompleteEvenGrid ((fwJointGridLabels base J).attach.image rowSlot)
      (fun x => fwPhysicalRowLayerGap a rows x.1 x.2) R ∧
    CompleteEvenGrid ((fwJointGridLabels base J).attach.image colSlot)
      (fun x => fwPhysicalColumnLayerGap a cols x.1 x.2) R ∧
    (∀ x side, LayerPacking.sequenceCell rows ((rowSlot x).1, ((rowSlot x).2, side)) =
      ((if side then p edge.1 edge.2 else edge.2), (rows.get (rowSlot x).1).2 edge.2)) ∧
    (∀ x side, (LayerPacking.sequenceCell cols ((colSlot x).1, ((colSlot x).2, side))).swap =
      ((cols.get (colSlot x).1).2 edge.2, (if side then p edge.1 edge.2 else edge.2))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact completeEvenGrid_finite_relabel (fwJointGridLabels base J) (Sum.elim rowBaseGap wide) R
      rowSlot hrowinj (fun x => fwPhysicalRowLayerGap a rows x.1 x.2) hrowgap hrowgrid
  · exact completeEvenGrid_finite_relabel (fwJointGridLabels base J) (Sum.elim colBaseGap wide) R
      colSlot hcolinj (fun x => fwPhysicalColumnLayerGap a cols x.1 x.2) hcolgap hcolgrid
  · intro x side
    obtain ⟨he, hp⟩ := hrowedge x
    cases side <;> simp [LayerPacking.sequenceCell, LayerPacking.layerCell, he]
    simpa using hp
  · intro x side
    obtain ⟨he, hp⟩ := hcoledge x
    cases side <;> simp [LayerPacking.sequenceCell, LayerPacking.layerCell, he]
    simpa using hp

end
end Sude
