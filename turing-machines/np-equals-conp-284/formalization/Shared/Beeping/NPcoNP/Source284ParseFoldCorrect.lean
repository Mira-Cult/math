import Shared.Beeping.NPcoNP.Source284ParseFoldStep
import Shared.Beeping.NPcoNP.Source284RawParse

/-! The parser fold implements the finite raw-list payload parser. One
explicit false bit supplies the source's virtual zero payload at end of input.
This is a finite extensional theorem, not a physical-machine refinement. -/

namespace Shared.Beeping.NPcoNP.Source284ParseFoldCorrect

open Shared.ComplexityBridge.TM2PolynomialFold
open Shared.Beeping.NPcoNP.Source284ParseFoldStep
open Shared.Beeping.NPcoNP.Source284RawParse

@[simp] theorem fold_cons (s : Packed) (b : Bool) (xs : List Bool) :
    fold step s (b :: xs) = fold step (step (s,b)) xs := rfl

/-- The stopped state retains its accumulator for any remaining input. -/
theorem fold_done (xs : List Bool) (acc : List Bool) :
    fold step ((true,false),acc) xs = ((true,false),acc) := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simpa [step, done, state] using ih

/-- The accumulator is reversed because payload bits are pushed at its head. -/
theorem fold_payload (xs : List Bool) : ∀ acc : List Bool,
    (fold step ((false,false),acc) (xs ++ [false])).2 =
      (payload xs).reverse ++ acc := by
  induction xs using List.twoStepInduction with
  | nil =>
    intro out
    simp [fold, step, done, pending, bit, acc, stop, state, payload]
  | singleton a =>
    intro out
    cases a <;> simp [fold, step, done, pending, bit, acc, stop, mark, consume, state, payload]
  | cons_cons a b bs ih _ =>
    intro out
    cases a with
    | false =>
      simp [fold_cons, step, done, pending, bit, acc, stop, state, payload, fold_done]
    | true =>
      simp only [List.cons_append, fold_cons]
      simp only [step, done, pending, bit, acc, stop, mark, consume, state,
        Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
      rw [ih]
      simp [payload, List.reverse_cons, List.append_assoc]

/-- Appending one zero to the real input handles the absent payload case. -/
theorem fold_correct (xs : List Bool) :
    (fold step ((false,false),[]) (xs ++ [false])).2 = (payload xs).reverse := by
  simpa using fold_payload xs []

end Shared.Beeping.NPcoNP.Source284ParseFoldCorrect
