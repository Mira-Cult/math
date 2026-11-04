import Shared.PNP.Record285.PythonControlRelocationStep

/-! Normalizing an already settled interpreter configuration changes neither
its complete state nor the next labelled step. -/
set_option maxRecDepth 8192
namespace Shared.PNP.Record285.PythonControlSettle
open Shared.PNP.Record285.PythonStraight
open Shared.PNP.Record285.PythonControl

theorem settle_idempotent (pc : Nat) (loops : List Loop) :
    settle (settle pc loops).1 (settle pc loops).2 = settle pc loops := by
  induction loops generalizing pc with
  | nil => rfl
  | cons loop rest ih =>
    by_cases h : loop.exit ≤ pc
    · simpa only [settle,if_pos h] using ih loop.head
    · simp [settle,h]

theorem step_settled (pc : Nat) (s : Store) (loops : List Loop)
    (target : Nat) (remaining : List Loop)
    (h : settle pc loops = (target,remaining)) :
    step code (.live ⟨pc,s,loops⟩) = step code (.live ⟨target,s,remaining⟩) := by
  have fixed := settle_idempotent pc loops
  rw [h] at fixed
  simp only at fixed
  simp only [step,h,fixed]

end Shared.PNP.Record285.PythonControlSettle
