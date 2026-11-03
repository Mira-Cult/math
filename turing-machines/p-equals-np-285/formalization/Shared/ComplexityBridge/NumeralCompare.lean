import Shared.ComplexityBridge.TM2NumeralNormalize

namespace Shared.ComplexityBridge.NumeralCompare
open Shared.ComplexityBridge.NumeralNormalization

/-- Remaining normalized bits after a common prefix whose last bit is `last`. -/
def suffix (last : Option Bool) (xs : List Bool) : List Bool :=
  xs ++ if lastSeen xs last = some false then [true] else []

theorem suffix_initial (xs : List Bool) : suffix none xs = normalize xs := rfl

theorem suffix_cons (last : Option Bool) (b : Bool) (xs : List Bool) :
    suffix last (b::xs) = b::suffix (some b) xs := rfl

theorem suffix_nil_cons_iff (last : Option Bool) (b : Bool) (xs : List Bool) :
    suffix last [] = suffix last (b::xs) ↔ last = some false ∧ b = true ∧ xs = [] := by
  cases last with
  | none => cases b <;> cases xs <;> simp [suffix,lastSeen]
  | some a => cases a <;> cases b <;> cases xs <;> simp [suffix,lastSeen]

end Shared.ComplexityBridge.NumeralCompare
