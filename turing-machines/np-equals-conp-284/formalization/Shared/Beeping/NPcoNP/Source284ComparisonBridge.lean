import Shared.Beeping.NPcoNP.Source284Comparison
import Shared.Beeping.NPcoNP.Source284Truncation
import Shared.Beeping.Controller

/-! Connect the pinned source comparison to its reference oversupply proof
and to the shared atomic rejection controller. This is not a compiler or
physical-machine refinement, nor a complexity-class characterization. -/
namespace Shared.Beeping.NPcoNP.Source284Comparison

open Shared.Beeping.NPcoNP.Source284Relative

/-- All four possible reference/candidate bit pairs, including both distinct
failure cases `(false,false)` and `(true,true)`. -/
theorem sourceToggle_table :
    sourceToggle false false = false ∧ sourceToggle false true = true ∧
    sourceToggle true false = true ∧ sourceToggle true true = false := by
  decide

/-- The source's final zero check is exactly equality of the two bits. -/
theorem sourceToggle_failure_iff (a b : Bool) :
    sourceToggle a b = false ↔ a = b := by
  cases a <;> cases b <;> decide

/-- The source's D(i) attempts have exactly the acceptance value of the
canonical `2^N(i)` certificate range. -/
theorem reference_exact (i : Nat) :
    reference i = acceptBound (Source284Parser.description i) 0
      (Source284Parser.length i) (2 ^ Source284Parser.length i) :=
  acceptBound_oversupply (Source284Parser.description i) 0
    (Source284Parser.length i) (Source284Parser.description i)
    (Source284Parser.sentinel_bounds i).1

/-- Equal output bits are precisely the two failing cases. -/
theorem compare_xor (j i : Nat) :
    compare j i = Bool.xor (reference i) (candidate j i) := by
  cases h₁ : reference i <;> cases h₂ : candidate j i <;>
    simp [compare, h₁, h₂, Bool.xor]

theorem compare_true_iff_complement (j i : Nat) :
    compare j i = true ↔ candidate j i = !reference i := by
  cases h₁ : reference i <;> cases h₂ : candidate j i <;>
    simp [compare, h₁, h₂]

/-- The atomic controller's first beep and one beep per rejected candidate
give eventual silence exactly when some source-specific candidate passes
every natural-number test. -/
theorem controller_silent_iff :
    (Shared.Beeping.Controller.system compare 0).EventuallySilent ↔
      ∃ j, ∀ i, candidate j i = !reference i := by
  rw [Shared.Beeping.Controller.eventuallySilent_zero_iff_exists_good]
  simp only [Shared.Beeping.Controller.Good, compare_true_iff_complement]

end Shared.Beeping.NPcoNP.Source284Comparison
