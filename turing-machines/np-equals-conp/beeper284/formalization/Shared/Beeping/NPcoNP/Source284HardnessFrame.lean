import Shared.Beeping.NPcoNP.Source284Suffix
import Shared.Beeping.NPcoNP.Source284ComparisonBridge
import Shared.ComplexityBridge.CircuitPairComputability

/-! A concrete bitstring wrapper for reductions to the selected source
reference. The source's time bound is the marker/payload count, and its
program is the payload with a leading sentinel bit. This module proves the
exact accepted relation and output size. It neither proves polynomial-time
execution of this wrapper nor that adding the sentinel preserves a supplied
program's behavior. -/

namespace Shared.Beeping.NPcoNP.Source284HardnessFrame

open Shared.Beeping.NPcoNP.Source284Parser
open Shared.Beeping.NPcoNP.Source284Comparison
open Shared.Beeping.NPcoNP.Source284Relative
open Shared.Codes.BitNumeralCompare

/-- Code bits are low-endian. High zero padding extends the source clock;
the frame parser reads the payload in the opposite order. -/
def input (code : List Bool) (padding : Nat) : List Bool :=
  frameBits (code ++ List.replicate padding false).reverse []

def clock (code : List Bool) (padding : Nat) : Nat := code.length + padding

def description (code : List Bool) (padding : Nat) : Nat :=
  2 ^ clock code padding + value code

@[simp] theorem value_replicate_false (n : Nat) : value (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, value, ih]

@[simp] theorem value_padding (code : List Bool) (padding : Nat) :
    value (code ++ List.replicate padding false) = value code := by
  rw [bitValue_append]
  simp

@[simp] theorem frameBits_length (xs ys : List Bool) :
    (frameBits xs ys).length = 2 * xs.length + 1 + ys.length := by
  induction xs with
  | nil => simp [frameBits, Nat.add_comm]
  | cons b bs ih => simp [frameBits, ih]; omega

/-- Every output bit is counted, including the terminating zero marker. -/
theorem input_length (code : List Bool) (padding : Nat) :
    (input code padding).length = 2 * clock code padding + 1 := by
  simp [input, clock, frameBits_length, Nat.add_comm]

theorem input_parse (code : List Bool) (padding : Nat) :
    parse (value (input code padding)) =
      (clock code padding, description code padding) := by
  unfold input
  rw [parse_value_frameBits, payloadFold_value]
  simp [clock, description, Nat.add_comm]

theorem input_length_field (code : List Bool) (padding : Nat) :
    Source284Parser.length (value (input code padding)) = clock code padding := by
  simpa [Source284Parser.length] using congrArg Prod.fst (input_parse code padding)

theorem input_description_field (code : List Bool) (padding : Nat) :
    Source284Parser.description (value (input code padding)) = description code padding := by
  simpa [Source284Parser.description] using congrArg Prod.snd (input_parse code padding)

/-- Source reference acceptance on the generated input is exactly bounded
acceptance of the *sentinel-extended* program, started with zero input and
all certificates below `2^clock`. -/
theorem reference_input (code : List Bool) (padding : Nat) :
    reference (value (input code padding)) =
      acceptBound (description code padding) 0 (clock code padding)
        (2 ^ clock code padding) := by
  rw [reference_exact, input_length_field, input_description_field]

/-- Same statement with the concrete bounded existential witness semantics. -/
theorem reference_input_iff (code : List Bool) (padding : Nat) :
    reference (value (input code padding)) = true ↔
      ∃ certificate, certificate < 2 ^ clock code padding ∧
        accepts (description code padding) 0 certificate (clock code padding) = true := by
  rw [reference_input, acceptBound_iff]

/-- The sentinel is real program data. Without a separating zero, it can
change even the first transition's acceptance result. -/
theorem sentinel_can_change_acceptance :
    accepts 7 0 0 1 = true ∧ accepts 15 0 0 1 = false := by
  have h7 : record 7 0 = 3 := by
    simp [record, dropRecords, readRecord_odd 7 (by decide),
      readRecord_odd 3 (by decide), readRecord_odd 1 (by decide)]
  have h15 : record 15 0 = 4 := by
    simp [record, dropRecords, readRecord_odd 15 (by decide),
      readRecord_odd 7 (by decide), readRecord_odd 3 (by decide),
      readRecord_odd 1 (by decide)]
  simp [accepts, Source284Relative.run, initial, step, h7, h15]

theorem frameOnly_primrec : Primrec (fun xs : List Bool => frameBits xs []) := by
  let S := Bool × List Bool × List Bool
  have hstep : Primrec₂ (fun (_ : List Bool) (s : S) => true :: s.1 :: s.2.2) := by
    exact (Primrec.list_cons.comp (Primrec.const true)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).to₂
  have h := Primrec.list_rec (Primrec.id : Primrec (id : List Bool → List Bool))
    (Primrec.const ([false] : List Bool)) hstep
  apply h.of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    change true :: b :: (List.recOn bs [false] (fun bit _ acc => true :: bit :: acc)) =
      true :: b :: frameBits bs []
    exact congrArg (fun ys => true :: b :: ys) ih

/-- The input constructor is executable; the primitive-recursion proof is
qualitative and does not assert a polynomial bit-operation runtime. -/
theorem input_primrec : Primrec₂ input := by
  have hcode : Primrec (fun p : List Bool × Nat => p.1) := Primrec.fst
  have hp : Primrec (fun p : List Bool × Nat => List.replicate p.2 false) :=
    Shared.ComplexityBridge.CircuitPairComputability.replicateFalse_primrec.comp Primrec.snd
  have hpadded : Primrec (fun p : List Bool × Nat => p.1 ++ List.replicate p.2 false) :=
    Primrec.list_append.comp hcode hp
  exact (frameOnly_primrec.comp (Primrec.list_reverse.comp hpadded)).to₂

theorem input_computable : Computable₂ input := input_primrec.to_comp

end Shared.Beeping.NPcoNP.Source284HardnessFrame
