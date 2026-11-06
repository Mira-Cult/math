import Shared.Beeping.NPcoNP.Source284Comparison
import Shared.ComplexityBridge.ClockBounds

/-! Fixed polynomial bounds for the 284 source clock on the strictly positive
prefix-length domain. This is an arithmetic ingredient of candidate coverage,
not a simulation-time bound for any particular verifier. The zero-length
boundary has clock one and is deliberately excluded. -/

namespace Shared.Beeping.NPcoNP.Source284Comparison

/-- For positive prefix length, one exponent, independent of the input,
absorbs any supplied natural-coefficient polynomial. Every larger exponent
also works, which is needed when a description number is padded upward. -/
theorem positive_prefix_polynomial_bound (p : Polynomial Nat) :
    ∃ k : Nat, ∀ (j i : Nat), k ≤ j → 0 < Source284Parser.length i →
      p.eval (Source284Parser.length i) ≤ clock j i := by
  obtain ⟨k, hk⟩ := Shared.ComplexityBridge.ClockBounds.polynomial_fixed_exponent p
  refine ⟨2 * k, ?_⟩
  intro j i hj hi
  let n := Source284Parser.length i
  have hn : 0 < n := hi
  have hbase : n + 2 ≤ (n + 1) ^ 2 := by nlinarith
  calc
    p.eval n ≤ (n + 2) ^ k := hk n
    _ ≤ ((n + 1) ^ 2) ^ k := Nat.pow_le_pow_left hbase k
    _ = (n + 1) ^ (2 * k) := by rw [← pow_mul]
    _ ≤ (n + 1) ^ j := Nat.pow_le_pow_right (by omega) hj
    _ = clock j i := rfl

end Shared.Beeping.NPcoNP.Source284Comparison
