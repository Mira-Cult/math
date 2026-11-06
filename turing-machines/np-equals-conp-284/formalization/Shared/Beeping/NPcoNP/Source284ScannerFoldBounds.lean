import Shared.Beeping.NPcoNP.Source284ScannerFoldStep
import Shared.ComplexityBridge.Encodings

/-! Prefix-state space bounds for the source 284 scanner fold. These bounds
count the actual canonical encoded bits. They do not assert that the fold or
the full record scanner executes in polynomial time. -/

namespace Shared.Beeping.NPcoNP.Source284ScannerFoldBounds

open Shared.Beeping.NPcoNP.Source284ScannerFoldStep
open Shared.Beeping.NPcoNP.Source284RecordBitCost
open Shared.ComplexityBridge

/-- A scan step never changes the fixed width of the binary index. -/
theorem step_index_length (s : State) (b : Bool) :
    (step (s,b)).2.1.length = s.2.1.length := by
  rcases s with ⟨d,idx,as⟩
  cases d <;> cases b <;> cases hz : isZero idx <;>
    simp [step, state, done, fields, index, acc, bit, zero, grow, stop,
      descend, hz, decBits_length]

/-- A scan step adds at most one unary result bit. -/
theorem step_acc_length (s : State) (b : Bool) :
    (step (s,b)).2.2.length ≤ s.2.2.length + 1 := by
  rcases s with ⟨d,idx,as⟩
  cases d <;> cases b <;> cases hz : isZero idx <;>
    simp [step, state, done, fields, index, acc, bit, zero, grow, stop,
      descend, hz]

/-- Every finite prefix retains index width, and grows the output by no more
than one bit per processed code bit. -/
theorem fold_lengths (s : State) (code : List Bool) :
    (TM2PolynomialFold.fold step s code).2.1.length = s.2.1.length ∧
      (TM2PolynomialFold.fold step s code).2.2.length ≤ s.2.2.length + code.length := by
  induction code generalizing s with
  | nil => simp [TM2PolynomialFold.fold]
  | cons b bs ih =>
    change (TM2PolynomialFold.fold step (step (s,b)) bs).2.1.length = s.2.1.length ∧
      (TM2PolynomialFold.fold step (step (s,b)) bs).2.2.length ≤ s.2.2.length + (b :: bs).length
    obtain ⟨hi,ha⟩ := ih (step (s,b))
    have hs := step_index_length s b
    have ht := step_acc_length s b
    constructor
    · exact hi.trans hs
    · simp only [List.length_cons]
      omega

/-- Exact serialization size for the canonical nested pair state. -/
theorem state_encoded_length (s : State) :
    (BitstringEncoding.bitEncode s).length = 6 * s.2.1.length + 3 * s.2.2.length + 4 := by
  rcases s with ⟨d,idx,as⟩
  change (BitstringEncoding.delimit (BitstringEncoding.bitEncode d) ++
    (BitstringEncoding.delimit (BitstringEncoding.bitEncode idx) ++ BitstringEncoding.bitEncode as)).length = _
  simp only [List.length_append, BitstringEncoding.length_delimit, bitstring_list_encoded_length]
  have hb : (BitstringEncoding.bitEncode d).length = 1 := by cases d <;> rfl
  rw [hb]
  omega

/-- The fold state encoded after any supplied prefix has linear size in its
initial fixed-width index and the total number of processed code bits. -/
theorem fold_state_encoded_bound (s : State) (code : List Bool) :
    (BitstringEncoding.bitEncode (TM2PolynomialFold.fold step s code)).length ≤
      6 * s.2.1.length + 3 * (s.2.2.length + code.length) + 4 := by
  rw [state_encoded_length]
  obtain ⟨hi,ha⟩ := fold_lengths s code
  rw [hi]
  omega

/-- For the actual scanner initialization, any `take` prefix is bounded by
the full raw `(index, code)` input, including redundant high zero bits. -/
theorem initial_prefix_encoded_bound (idx code : List Bool) (k : Nat) :
    (BitstringEncoding.bitEncode (TM2PolynomialFold.fold step (false,(idx,[])) (code.take k))).length ≤
      (BitstringEncoding.bitEncode (idx,code)).length + 3 := by
  have h := fold_state_encoded_bound (false,(idx,[])) (code.take k)
  rw [bitstring_pair_encoded_length]
  simp only [List.length_nil, Nat.zero_add] at h
  have hk := (List.take_sublist k code).length_le
  omega

/-- The generic fold I/O wrapper represents the same state as
`((done,index),accumulator)`; include both tuple delimiters in its size. -/
def packed (s : State) : (Bool × List Bool) × List Bool :=
  ((s.1,s.2.1),s.2.2)

theorem packed_encoded_length (s : State) :
    (BitstringEncoding.bitEncode (packed s)).length =
      6 * s.2.1.length + 3 * s.2.2.length + 7 := by
  rcases s with ⟨d,idx,as⟩
  change (BitstringEncoding.delimit
      (BitstringEncoding.delimit (BitstringEncoding.bitEncode d) ++ BitstringEncoding.bitEncode idx) ++
      BitstringEncoding.bitEncode as).length = _
  simp only [List.length_append, BitstringEncoding.length_delimit, bitstring_list_encoded_length]
  have hb : (BitstringEncoding.bitEncode d).length = 1 := by cases d <;> rfl
  rw [hb]
  omega

theorem initial_packed_bound_of_length (d : Bool) (idx pref code : List Bool)
    (hp : pref.length ≤ code.length) :
    (BitstringEncoding.bitEncode (packed
      (TM2PolynomialFold.fold step (d,(idx,[])) pref))).length ≤
      (BitstringEncoding.bitEncode ((d,idx),code)).length := by
  rw [packed_encoded_length]
  have h := fold_lengths (d,(idx,[])) pref
  change _ ≤ (BitstringEncoding.delimit
    (BitstringEncoding.delimit (BitstringEncoding.bitEncode d) ++ BitstringEncoding.bitEncode idx) ++
      BitstringEncoding.bitEncode code).length
  simp only [List.length_append, BitstringEncoding.length_delimit, bitstring_list_encoded_length]
  have hbool : (BitstringEncoding.bitEncode d).length = 1 := by cases d <;> rfl
  rw [hbool]
  simp only [List.length_nil, Nat.zero_add] at h
  omega

theorem initial_packed_prefix_bound (d : Bool) (idx code : List Bool) (k : Nat) :
    (BitstringEncoding.bitEncode (packed
      (TM2PolynomialFold.fold step (d,(idx,[])) (code.take k)))).length ≤
      (BitstringEncoding.bitEncode ((d,idx),code)).length := by
  exact initial_packed_bound_of_length d idx (code.take k) code (List.take_sublist k code).length_le

/-- The serialized step request includes the whole state as a delimited
first component and a single Boolean item. -/
theorem initial_packed_step_input_bound (d : Bool) (idx pref code : List Bool)
    (hp : pref.length ≤ code.length) (b : Bool) :
    (BitstringEncoding.bitEncode (packed
      (TM2PolynomialFold.fold step (d,(idx,[])) pref),b)).length ≤
      2 * (BitstringEncoding.bitEncode ((d,idx),code)).length + 2 := by
  have h := initial_packed_bound_of_length d idx pref code hp
  change (BitstringEncoding.delimit (BitstringEncoding.bitEncode (packed
      (TM2PolynomialFold.fold step (d,(idx,[])) pref))) ++ BitstringEncoding.bitEncode b).length ≤ _
  simp only [List.length_append, BitstringEncoding.length_delimit]
  have hb : (BitstringEncoding.bitEncode b).length = 1 := by cases b <;> rfl
  rw [hb]
  omega

end Shared.Beeping.NPcoNP.Source284ScannerFoldBounds
