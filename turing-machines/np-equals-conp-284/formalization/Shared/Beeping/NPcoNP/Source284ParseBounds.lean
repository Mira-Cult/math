import Shared.ComplexityBridge.TM2PolynomialFold
import Shared.ComplexityBridge.Encodings

/-! Encoding bounds for a parser fold with two Boolean control flags and a
single accumulated Boolean list.  These are generic bounds, independent of
the parser transition function or its execution cost. -/

namespace Shared.Beeping.NPcoNP.Source284ParseBounds

open Shared.ComplexityBridge
open Shared.ComplexityBridge.TM2PolynomialFold

/-- The exact canonical encoded length, including both pair delimiters. -/
theorem encoded_length (flags : Bool × Bool) (acc : List Bool) :
    (BitstringEncoding.bitEncode (flags, acc)).length = 3 * acc.length + 9 := by
  rcases flags with ⟨d, p⟩
  change (BitstringEncoding.delimit
    (BitstringEncoding.delimit (BitstringEncoding.bitEncode d) ++ BitstringEncoding.bitEncode p) ++
      BitstringEncoding.bitEncode acc).length = _
  simp only [List.length_append, BitstringEncoding.length_delimit, bitstring_list_encoded_length]
  have hd : (BitstringEncoding.bitEncode d).length = 1 := by cases d <;> rfl
  have hp : (BitstringEncoding.bitEncode p).length = 1 := by cases p <;> rfl
  rw [hd, hp]
  omega

/-- A fold whose step appends at most one bit to its output list accumulates
at most one list cell per input bit, for every starting state. -/
theorem fold_acc_length (step : (((Bool × Bool) × List Bool) × Bool) →
    ((Bool × Bool) × List Bool))
    (hstep : ∀ state bit, (step (state, bit)).2.length ≤ state.2.length + 1)
    (state : (Bool × Bool) × List Bool) (xs : List Bool) :
    (fold step state xs).2.length ≤ state.2.length + xs.length := by
  induction xs generalizing state with
  | nil => simp [fold]
  | cons b bs ih =>
    change (fold step (step (state,b)) bs).2.length ≤ state.2.length + (b :: bs).length
    have hi := ih (step (state,b))
    have hs := hstep state b
    simp only [List.length_cons]
    omega

/-- The generic TM2 fold's empty-accumulator start and any prefix use no more
encoded state bits than the full `(flags,input)` pair. -/
theorem fold_prefix_encoded_bound
    (step : (((Bool × Bool) × List Bool) × Bool) → ((Bool × Bool) × List Bool))
    (hstep : ∀ state bit, (step (state, bit)).2.length ≤ state.2.length + 1)
    (flags : Bool × Bool) (xs pref tail : List Bool) (hxs : xs = pref ++ tail) :
    (BitstringEncoding.bitEncode (fold step (flags,[]) pref)).length ≤
      (BitstringEncoding.bitEncode (flags,xs)).length := by
  rw [encoded_length, encoded_length]
  have h := fold_acc_length step hstep (flags,[]) pref
  simp only [List.length_nil, Nat.zero_add] at h
  have hp : pref.length ≤ xs.length := by rw [hxs, List.length_append]; omega
  omega

end Shared.Beeping.NPcoNP.Source284ParseBounds
