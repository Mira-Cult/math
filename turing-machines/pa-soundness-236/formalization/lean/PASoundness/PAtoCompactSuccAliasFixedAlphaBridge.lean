import PASoundness.PAtoCompactQuotSuccWitnessFresh
import PASoundness.PAtoCompactQuotSuccNamedEncoding
import PASoundness.PAtoCompactSuccBaseMultiAlpha

/-! Capture-safe finite-K alpha bridges between the two fixed endpoint-alias
quotient-successor formulas and versions allocated in block 100. This does not
eliminate endpoint equality guards or prove the cancellation theorem. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccAliasFixedAlphaBridge
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactQuotSuccWitnessFresh
open PASoundness.PAtoCompactSuccBaseSyntax PASoundness.PAtoCompactSuccBaseInventory
open PASoundness.PAtoCompactMultiAlpha PASoundness.PAtoCompactSafeStepsInitial
open PASoundness.PAtoCompactAlphaMapOne PASoundness.PAtoCompactEquivNoShadow

def fixedSteps : List (Nat × Nat) := succOffsets.map (fun k => (k, 102+k))

theorem first_binders : firstAliases.binders = successorTemplate.binders := by decide
theorem second_binders : secondAliases.binders = successorTemplate.binders := by decide

theorem first_allNoShadow (x : Nat) : NoShadow x firstAliases := by
  by_cases hx : x ∈ firstAliases.binders
  · rw [first_binders, successor_binders] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · exact noShadow_of_not_binder _ _ hx

theorem second_allNoShadow (x : Nat) : NoShadow x secondAliases := by
  by_cases hx : x ∈ secondAliases.binders
  · rw [second_binders, successor_binders] at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · exact noShadow_of_not_binder _ _ hx

theorem first_safe : InitialSafe fixedSteps firstAliases := by
  refine ⟨?_, ?_, first_allNoShadow⟩
  · intro p hp
    simp only [fixedSteps, succOffsets, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · decide

theorem second_safe : InitialSafe fixedSteps secondAliases := by
  refine ⟨?_, ?_, second_allNoShadow⟩
  · intro p hp
    simp only [fixedSteps, succOffsets, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · decide

theorem first_shape : renameSteps fixedSteps firstAliases = succAt 100 40 41 := by decide
theorem second_shape : renameSteps fixedSteps secondAliases = succAt 100 42 43 := by decide

/-- The first fixed quotient-successor alias formula and its fresh-block
allocated version are equivalent by a finite K alpha proof. -/
def first_alpha : ProofEquiv firstAliases (succAt 100 40 41) := by
  have h := multiAlpha fixedSteps firstAliases (initial_safe_steps fixedSteps firstAliases first_safe)
  rw [first_shape] at h
  exact h

/-- The second alias formula has the analogous independent alpha proof. -/
def second_alpha : ProofEquiv secondAliases (succAt 100 42 43) := by
  have h := multiAlpha fixedSteps secondAliases (initial_safe_steps fixedSteps secondAliases second_safe)
  rw [second_shape] at h
  exact h

end PASoundness.PAtoCompactSuccAliasFixedAlphaBridge

#print axioms PASoundness.PAtoCompactSuccAliasFixedAlphaBridge.first_alpha
#print axioms PASoundness.PAtoCompactSuccAliasFixedAlphaBridge.second_alpha
