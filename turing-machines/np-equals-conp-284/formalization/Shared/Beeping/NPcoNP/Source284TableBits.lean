import Shared.Beeping.NPcoNP.Source284RecordEncoding
import Shared.Beeping.NPcoNP.Source284RecordBits
import Shared.Codes.BitNumeralCompare

/-! Literal little-endian source record words. The lists supplied as record
values are unary: only their lengths matter. Every record has an explicit
zero terminator; a finite high tail is kept separate. These are encoding
identities, not a runtime or table-compiler correctness theorem. -/

namespace Shared.Beeping.NPcoNP.Source284TableBits

open Shared.Beeping.NPcoNP.Source284Relative
open Shared.Codes.BitNumeralCompare (value)

/-- The explicit source word `1^|xs| 0` for a unary input record. -/
def recordWord (xs : List Bool) : List Bool :=
  xs.map (fun _ => true) ++ [false]

/-- Low-order record words followed by the supplied high-order tail. -/
def unaryRecords (xss : List (List Bool)) (tail : List Bool) : List Bool :=
  (xss.map recordWord).flatten ++ tail

@[simp] theorem recordWord_length (xs : List Bool) :
    (recordWord xs).length = xs.length + 1 := by
  simp [recordWord]

/-- The literal word has exactly the value of the numeric source encoder. -/
theorem recordWord_value (xs tail : List Bool) :
    value (recordWord xs ++ tail) = encodeRecord xs.length (value tail) := by
  induction xs with
  | nil => simp [recordWord, value, encodeRecord]
  | cons b xs ih =>
    simp only [recordWord, List.map_cons, List.cons_append, List.length_cons,
      value, encodeRecord] at *
    rw [ih]
    simp

/-- Every finite literal bit encoding agrees with the source's numeric
record encoding, including an arbitrary finite high-order tail. -/
theorem unaryRecords_value (xss : List (List Bool)) (tail : List Bool) :
    value (unaryRecords xss tail) =
      encodeRecords (xss.map List.length) (value tail) := by
  induction xss with
  | nil => simp [unaryRecords, encodeRecords]
  | cons xs xss ih =>
    simp only [unaryRecords, List.map_cons, List.flatten_cons, List.append_assoc,
      encodeRecords] at *
    rw [recordWord_value, ih]

/-- The exact serialized bit length includes one delimiter per record. -/
theorem unaryRecords_length (xss : List (List Bool)) (tail : List Bool) :
    (unaryRecords xss tail).length =
      (xss.map (fun xs => xs.length + 1)).sum + tail.length := by
  induction xss with
  | nil => simp [unaryRecords]
  | cons xs xss ih =>
    simp only [unaryRecords, List.map_cons, List.flatten_cons, List.length_append,
      List.sum_cons, recordWord_length] at *
    omega

/-- Every encoded record is read back with its prescribed unary length,
regardless of the remaining records and the supplied high-order tail. -/
theorem unaryRecords_lookup (xss : List (List Bool)) (tail : List Bool)
    (i : Nat) (hi : i < xss.length) :
    Source284RecordBits.recordBits (unaryRecords xss tail) i = (xss[i]).length := by
  calc
    Source284RecordBits.recordBits (unaryRecords xss tail) i =
        record (value (unaryRecords xss tail)) i :=
      (Source284RecordBits.recordBits_correct _ _).symm
    _ = record (encodeRecords (xss.map List.length) (value tail)) i := by
      rw [unaryRecords_value]
    _ = (xss[i]).length := by
      have hmap : i < (xss.map List.length).length := by simpa using hi
      have h := record_encodeRecords (xss.map List.length) (value tail) i hmap
      rw [List.getElem_map] at h
      exact h

/-- Empty high tail gives the zero-tail source program; no record can merge
with a later word because each finite word carries its delimiter. -/
theorem zeroTail_value (xss : List (List Bool)) :
    value (unaryRecords xss []) = encodeRecords (xss.map List.length) 0 := by
  simpa [value] using unaryRecords_value xss []

end Shared.Beeping.NPcoNP.Source284TableBits
