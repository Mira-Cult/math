import Shared.Beeping.NPcoNP.Source284Suffix

/-! A size bound for the exact marker/payload input framing. This bounds the
number of parser iterations in terms of the numerical input; it is not a
Turing-machine bit-cost or compiler-simulation theorem. -/
namespace Shared.Beeping.NPcoNP.Source284Parser

/-- Every marked pair consumes two bit positions, irrespective of the
payload and the arbitrary higher suffix. -/
theorem frame_exponential_bound (bits : List Bool) (suffix : Nat) :
    4 ^ bits.length ≤ 3 * encodeFrame bits suffix + 1 := by
  induction bits with
  | nil => simp [encodeFrame]
  | cons b bs ih =>
    simp only [encodeFrame, List.length_cons, pow_succ]
    cases b <;> simp <;> nlinarith

/-- The source's parsed length cannot grow faster than the bit length of
the original natural input, even if its ignored suffix is arbitrary. -/
theorem parsed_length_bound (i : Nat) : 4 ^ length i ≤ 3 * i + 1 := by
  obtain ⟨bits, suffix, rfl⟩ := encodeFrame_surjective i
  rw [(frame_length_description bits suffix).1]
  exact frame_exponential_bound bits suffix

theorem parsed_length_log2 (i : Nat) :
    2 * length i ≤ Nat.log2 (3 * i + 1) := by
  apply (Nat.le_log2 (by omega)).2
  rw [Nat.pow_mul]
  exact parsed_length_bound i

end Shared.Beeping.NPcoNP.Source284Parser
