import Sude.ProtectedPoolCells
import Sude.BridgePhysical

/-! Total-cell capacity for values protected in the exact prescribed pool. -/
namespace Sude
noncomputable section

/-- Exact intersection capacity supplies distinct cells avoiding the original
positions of all supplied values that occur in the pool. This is only a total
capacity result; no row, column, or diagonal arrangement is asserted. -/
theorem protectedPoolCells_free_cells_of_inter_card {n k : ℕ}
    (a : Cell n ≃ Fin (n * n)) (values : Finset ℕ)
    (hcapacity : 4 * k + (values ∩ poolFinset n).card ≤ n * n) :
    ∃ cells : Fin k × Fin 4 → Cell n,
      Function.Injective cells ∧ ∀ x, cells x ∉ protectedPoolCells a values := by
  have hcard := protectedPoolCells_card a values
  have hfit : 1 * k * 4 + (protectedPoolCells a values).card ≤ n * n := by omega
  obtain ⟨chosen, hinj, hfree⟩ :=
    bridge_stage_cells_of_capacity 1 k (protectedPoolCells a values) hfit
  refine ⟨fun x => chosen ((0, x.1), x.2), ?_, ?_⟩
  · intro x y heq
    have h := hinj heq
    exact Prod.ext (congrArg (fun z : (Fin 1 × Fin k) × Fin 4 => z.1.2) h)
      (congrArg (fun z : (Fin 1 × Fin k) × Fin 4 => z.2) h)
  · intro x
    exact hfree ((0, x.1), x.2)

/-- Counting every supplied value is a conservative sufficient capacity
condition, even if some supplied numbers are not pool values. This includes
all degenerate cases, such as `n=0` and `k=0`, allowed by the hypothesis. -/
theorem protectedPoolCells_free_cells_of_card {n k : ℕ}
    (a : Cell n ≃ Fin (n * n)) (values : Finset ℕ)
    (hcapacity : 4 * k + values.card ≤ n * n) :
    ∃ cells : Fin k × Fin 4 → Cell n,
      Function.Injective cells ∧ ∀ x, cells x ∉ protectedPoolCells a values := by
  apply protectedPoolCells_free_cells_of_inter_card a values
  have hcard := Finset.card_le_card (Finset.inter_subset_left : values ∩ poolFinset n ⊆ values)
  omega

end
end Sude
