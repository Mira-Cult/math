import Sude.ProtectedPoolCells
import Sude.ProtectedPoolCapacity

/-! Audit the protected-cell preimage and preservation interface. -/

#check Sude.protectedPoolCells_image
#print axioms Sude.protectedPoolCells_image
#check Sude.protectedPoolCells_card
#print axioms Sude.protectedPoolCells_card
#check Sude.protectedPoolCells_of_subset
#print axioms Sude.protectedPoolCells_of_subset
#check Sude.protectedPoolCells_preserve_value
#print axioms Sude.protectedPoolCells_preserve_value
#check Sude.protectedPoolCells_free_cells_of_inter_card
#print axioms Sude.protectedPoolCells_free_cells_of_inter_card
#check Sude.protectedPoolCells_free_cells_of_card
#print axioms Sude.protectedPoolCells_free_cells_of_card

example (a : Sude.Cell 0 ≃ Fin (0 * 0)) :
    ∃ cells : Fin 0 × Fin 4 → Sude.Cell 0,
      Function.Injective cells ∧ ∀ x, cells x ∉ Sude.protectedPoolCells a ∅ := by
  apply Sude.protectedPoolCells_free_cells_of_card a ∅
  norm_num
