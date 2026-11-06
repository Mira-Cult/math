import Mathlib.Computability.Partrec

/-!
One exhaustive, executable enumeration of raw Boolean-list inputs. This
uses mathlib's fixed `Encodable`/`Primcodable` natural-number coding, not
Google's `BitstringEncoding` serialization. Invalid natural codes yield the
empty list; repetitions are allowed. No cost or TM2 simulation bound is
asserted.
-/
namespace Shared.Codes.Inputs

def inputAt (n : Nat) : List Bool := (Encodable.decode n).getD []

@[simp] theorem inputAt_encode (bits : List Bool) : inputAt (Encodable.encode bits) = bits := by
  simp [inputAt]

theorem covers (bits : List Bool) : ∃ n, inputAt n = bits :=
  ⟨Encodable.encode bits, inputAt_encode bits⟩

theorem covers_empty : ∃ n, inputAt n = [] := covers []

/-- Recursion-theoretic computability for mathlib's `Primcodable` model.
This is not yet the requested quantitative bridge to Google's TM2 model. -/
theorem computable : Computable inputAt :=
  Computable.option_getD Computable.decode (Computable.const [])

/-- Agreement on the fixed enumeration is exactly agreement on all raw
bitstrings, including the empty input. -/
theorem agreement_iff (f g : List Bool → Bool) :
    (∀ n, f (inputAt n) = g (inputAt n)) ↔ ∀ bits, f bits = g bits := by
  constructor
  · intro h bits
    simpa using h (Encodable.encode bits)
  · intro h n
    exact h (inputAt n)

end Shared.Codes.Inputs
