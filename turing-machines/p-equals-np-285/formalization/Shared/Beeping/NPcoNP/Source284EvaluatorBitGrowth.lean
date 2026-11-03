import Shared.Beeping.NPcoNP.Source284EvaluatorBitStep
import Shared.ComplexityBridge.TM2PolynomialFold
import Shared.ComplexityBridge.Encodings

/-! Size bounds for the raw-bit-list bounded evaluator. The represented
numbers may have arbitrarily many high zero bits. These are bounds on the
data in the lists, not a running-time theorem for the evaluator. -/
namespace Shared.Beeping.NPcoNP.Source284EvaluatorBitGrowth

open Shared.Beeping.NPcoNP.Source284EvaluatorBitStep
open Shared.Beeping.NPcoNP.Source284RecordBitCost
open Shared.Beeping.NPcoNP.Source284RecordTM2
open Shared.ComplexityBridge

theorem size_le_self (n : Nat) : Nat.size n ≤ n :=
  Nat.size_le.mpr n.lt_two_pow_self

/-- The decoded record's binary representation is no longer than its
finite program input, even for noncanonical index encodings. -/
theorem lookup_bits_le (code idx : List Bool) :
    (lookup (code, idx)).bits.length ≤ code.length := by
  rw [Nat.size_eq_bits_len]
  exact le_trans (size_le_self _) (scan_length_le code idx)

def tapeLength (c : Config) : Nat := c.left.length + c.right.length

/-- A single evaluator transition adds at most one cell to the total of the
two explicitly represented tape halves. -/
theorem step_tapeLength (code : List Bool) (c : Config) :
    tapeLength (step code c) ≤ tapeLength c + 1 := by
  unfold step
  split
  · simp
  · dsimp only
    split <;> simp only [tapeLength, List.length_cons]
    all_goals have ht : c.right.tail.length ≤ c.right.length := by simp only [List.length_tail]; omega
    all_goals omega

/-- The new control bitstring is bounded by the program's bit length in an
active transition; an already-accepting control is retained unchanged. -/
theorem step_stateLength (code : List Bool) (c : Config) :
    (step code c).state.length ≤ max c.state.length code.length := by
  unfold step
  split
  · exact le_max_left _ _
  · dsimp only
    split <;> dsimp only
    all_goals
      have hb := lookup_bits_le code (ordinal c.state (c.right.headD false))
      have ht : (lookup (code, ordinal c.state (c.right.headD false))).bits.tail.tail.length ≤
          (lookup (code, ordinal c.state (c.right.headD false))).bits.length := by
        simp only [List.length_tail]
        omega
      omega

/-- A clock list supplies one source step per cell; its Boolean values do
not affect execution. -/
def clockStep (code : List Bool) (p : Config × Bool) : Config := step code p.1

theorem fold_lengths (code : List Bool) (c : Config) (clock : List Bool) :
    tapeLength (TM2PolynomialFold.fold (clockStep code) c clock) ≤
        tapeLength c + clock.length ∧
      (TM2PolynomialFold.fold (clockStep code) c clock).state.length ≤
        max c.state.length code.length := by
  induction clock generalizing c with
  | nil => simp [TM2PolynomialFold.fold]
  | cons b bs ih =>
    change tapeLength (TM2PolynomialFold.fold (clockStep code) (step code c) bs) ≤
        tapeLength c + (b :: bs).length ∧
      (TM2PolynomialFold.fold (clockStep code) (step code c) bs).state.length ≤
        max c.state.length code.length
    obtain ⟨ht, hs⟩ := ih (step code c)
    have hstep := step_tapeLength code c
    have hstate := step_stateLength code c
    constructor
    · simp only [List.length_cons]
      omega
    · exact le_trans hs (max_le hstate (le_max_right _ _))

/-- Full runtime data in the `σ` component of the generic fold. The
separate fold accumulator is initialized to the empty list. -/
def packed (code : List Bool) (c : Config) : (List Bool × (List Bool × List Bool)) × List Bool :=
  ((code,(c.left,c.right)),c.state)

theorem packed_encoded_length (code : List Bool) (c : Config) :
    (BitstringEncoding.bitEncode (packed code c)).length =
      12 * code.length + 12 * c.left.length + 6 * c.right.length + 3 * c.state.length + 5 := by
  change (BitstringEncoding.delimit
    (BitstringEncoding.delimit (BitstringEncoding.bitEncode code) ++
      (BitstringEncoding.delimit (BitstringEncoding.bitEncode c.left) ++
        BitstringEncoding.bitEncode c.right)) ++ BitstringEncoding.bitEncode c.state).length = _
  simp only [List.length_append, BitstringEncoding.length_delimit,
    bitstring_list_encoded_length]
  omega

/-- Every reached prefix, including empty and full prefixes, has an encoded
state bounded linearly in the full `(initial configuration, clock)` input.
The factor 8 accounts for the nested-pair delimiters and the dummy fold
accumulator. -/
theorem prefix_encoded_bound (code : List Bool) (c : Config) (clock pref tail : List Bool)
    (hclock : clock = pref ++ tail) :
    (BitstringEncoding.bitEncode
      (packed code (TM2PolynomialFold.fold (clockStep code) c pref), ([] : List Bool))).length ≤
      8 * (BitstringEncoding.bitEncode (packed code c,clock)).length := by
  have hlen : pref.length ≤ clock.length := by rw [hclock, List.length_append]; omega
  obtain ⟨ht, hs⟩ := fold_lengths code c pref
  have hs' : (TM2PolynomialFold.fold (clockStep code) c pref).state.length ≤
      c.state.length + code.length := le_trans hs (max_le (by omega) (by omega))
  change (BitstringEncoding.delimit (BitstringEncoding.bitEncode
      (packed code (TM2PolynomialFold.fold (clockStep code) c pref))) ++
      BitstringEncoding.bitEncode ([] : List Bool)).length ≤
    8 * (BitstringEncoding.delimit (BitstringEncoding.bitEncode (packed code c)) ++
      BitstringEncoding.bitEncode clock).length
  simp only [List.length_append, BitstringEncoding.length_delimit,
    bitstring_list_encoded_length, List.length_nil, Nat.mul_zero, Nat.add_zero]
  rw [packed_encoded_length, packed_encoded_length]
  simp only [tapeLength] at ht
  omega

end Shared.Beeping.NPcoNP.Source284EvaluatorBitGrowth
