import FormalConjecturesForMathlib.Computability.Complexity

/-!
Size lemmas for the actual `BitstringEncoding` instances imported by the
pinned Google complexity definitions. Lengths below count raw Boolean list
entries, not Turing-machine transition steps. No polynomial-time simulation
or SAT encoding is established here.
-/
namespace Shared.ComplexityBridge

/-- Google's canonical encoding of a raw Boolean list uses three bits per
input bit; in particular the empty list has encoded length zero. -/
theorem bitstring_list_encoded_length (x : List Bool) :
    (BitstringEncoding.bitEncode x).length = 3 * x.length := by
  change (((x.map fun b => [b]).map BitstringEncoding.delimit).flatten).length = 3 * x.length
  induction x with
  | nil => rfl
  | cons b xs ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append,
      BitstringEncoding.delimit, List.length_cons, List.length_nil, ih]
    omega

/-- Pair encoding delimits the encoded first list and appends the encoded
second list, so the first component contributes six bits per raw input bit. -/
theorem bitstring_pair_encoded_length (x w : List Bool) :
    (BitstringEncoding.bitEncode (x, w)).length = 6 * x.length + 1 + 3 * w.length := by
  change (BitstringEncoding.delimit (BitstringEncoding.bitEncode x) ++
    BitstringEncoding.bitEncode w).length = 6 * x.length + 1 + 3 * w.length
  simp only [List.length_append, BitstringEncoding.length_delimit, bitstring_list_encoded_length]
  omega

/-- A raw witness length bound gives the corresponding bound on the encoded
checker input. No runtime bound or polynomial-time closure is inferred. -/
theorem pair_encoded_length_le_of_witness_bound (x w : List Bool) (bound : Nat)
    (h : w.length ≤ bound) :
    (BitstringEncoding.bitEncode (x, w)).length ≤ 6 * x.length + 1 + 3 * bound := by
  rw [bitstring_pair_encoded_length]
  omega

end Shared.ComplexityBridge
