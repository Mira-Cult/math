import Shared.PNP.Record285.GrammarDeterministicLeaf

/-! Exact effects on an existing register, with the full preceding and
following bank retained. Extra cells introduced by physical normalization are
explicitly shown to be zero. This is an interface for a future coalescing proof;
it does not identify the registers with source variables. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.GrammarRegisterInterface
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.GrammarExact
open Shared.PNP.Record285.CleanBank
open Shared.PNP.Record285.GrammarOperationalRun

theorem increment_split (before after : List Nat) (value : Nat) :
    applyUpdate (.inc before.length) (before ++ [value] ++ after) =
      before ++ [value+1] ++ after := by
  have hp := split_parts before after value
  simp only [applyUpdate,hp.1,hp.2.1,hp.2.2]

theorem decrement_split (before after : List Nat) (value : Nat) :
    ∃ extra, applyUpdate (.dec before.length) (before ++ [value] ++ after) =
      (before ++ [value-1] ++ after) ++ List.replicate extra 0 := by
  have hp := split_parts before after value
  simp only [applyUpdate,hp.1,hp.2.1,hp.2.2]
  cases value with
  | zero => exact ⟨0,by simp [decrementFields]⟩
  | succ value => exact ⟨1,by simp [decrementFields,List.append_assoc]⟩

theorem half_split (before after : List Nat) (value : Nat) :
    ∃ extra, applyUpdate (.half before.length) (before ++ [value] ++ after) =
      (before ++ [value/2] ++ after) ++ List.replicate extra 0 := by
  have hp := split_parts before after value
  simp only [applyUpdate,hp.1,hp.2.1,hp.2.2]
  by_cases hz : value = 0
  · subst value
    exact ⟨0,by simp⟩
  by_cases ho : value = 1
  · subst value
    exact ⟨1,by simp [List.append_assoc]⟩
  by_cases he : value % 2 = 0
  · let n := (value-2)/2
    have hv : value / 2 = n+1 := by dsimp [n]; omega
    refine ⟨n+1,?_⟩
    simp only [hz,ho,he,if_false,if_true]
    change before ++ [n+1] ++ (after ++ List.replicate n 0) ++ [0] = _
    rw [hv, ← List.replicate_append_replicate]
    simp [List.append_assoc]
  · let n := (value-3)/2
    have hv : value / 2 = n+1 := by dsimp [n]; omega
    refine ⟨n+2,?_⟩
    simp only [hz,ho,he,if_false]
    change before ++ [n+1] ++ (after ++ List.replicate n 0) ++ [0,0] = _
    rw [hv, ← List.replicate_append_replicate]
    simp [List.append_assoc]

/-- The appended normalization cells cannot change any prefix that existed
before the decrement. -/
theorem decrement_existing_prefix (before after : List Nat) (value count : Nat)
    (hcount : count ≤ (before ++ [value] ++ after).length) :
    (applyUpdate (.dec before.length) (before ++ [value] ++ after)).take count =
      (before ++ [value-1] ++ after).take count := by
  obtain ⟨extra,h⟩ := decrement_split before after value
  rw [h, List.take_append_of_le_length]
  simpa using hcount

/-- Halving preserves the existing nonselected register prefix in the same
sense, including the zero and odd cases. -/
theorem half_existing_prefix (before after : List Nat) (value count : Nat)
    (hcount : count ≤ (before ++ [value] ++ after).length) :
    (applyUpdate (.half before.length) (before ++ [value] ++ after)).take count =
      (before ++ [value/2] ++ after).take count := by
  obtain ⟨extra,h⟩ := half_split before after value
  rw [h, List.take_append_of_le_length]
  simpa using hcount

/-- At the physical machine's certified action boundaries the same finite
register frame theorem applies to the actual selected decrement. -/
theorem physical_decrement_prefix (n : Nat) (before after : List Nat) (value count : Nat)
    (hfields : (operationSystem.run n).fields = before ++ [value] ++ after)
    (hedge : (chooseStep (operationSystem.run n)).edge = .dec before.length)
    (hcount : count ≤ (before ++ [value] ++ after).length) :
    (operationSystem.run (n+1)).fields.take count =
      (before ++ [value-1] ++ after).take count := by
  rw [(operation_step_computable_data n).2.2, hedge, hfields]
  exact decrement_existing_prefix before after value count hcount

/-- The same guarantee for a physical native-half action. -/
theorem physical_half_prefix (n : Nat) (before after : List Nat) (value count : Nat)
    (hfields : (operationSystem.run n).fields = before ++ [value] ++ after)
    (hedge : (chooseStep (operationSystem.run n)).edge = .half before.length)
    (hcount : count ≤ (before ++ [value] ++ after).length) :
    (operationSystem.run (n+1)).fields.take count =
      (before ++ [value/2] ++ after).take count := by
  rw [(operation_step_computable_data n).2.2, hedge, hfields]
  exact half_existing_prefix before after value count hcount

/-- Increment preserves the complete following bank without normalization. -/
theorem physical_increment (n : Nat) (before after : List Nat) (value : Nat)
    (hfields : (operationSystem.run n).fields = before ++ [value] ++ after)
    (hedge : (chooseStep (operationSystem.run n)).edge = .inc before.length) :
    (operationSystem.run (n+1)).fields = before ++ [value+1] ++ after := by
  rw [(operation_step_computable_data n).2.2, hedge, hfields]
  exact increment_split before after value
end Shared.PNP.Record285.GrammarRegisterInterface
