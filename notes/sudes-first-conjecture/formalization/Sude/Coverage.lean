import Mathlib.Algebra.Ring.Parity
import Lean.Elab.Tactic.Omega

namespace Sude

/-- Interval cover; the equivalence with the original integer-power
predicates is proved below. Controller correctness remains open. -/
def Route (n : ℕ) : Prop :=
  (2001 ≤ n ∧ n ≤ 19483) ∨ (19485 ≤ n ∧ n ≤ 27553) ∨
  (27555 ≤ n ∧ n ≤ 35733) ∨ (35735 ≤ n ∧ n ≤ 38967) ∨
  (38969 ≤ n ∧ n ≤ 46339) ∨ (46341 ≤ n ∧ n ≤ 55107) ∨
  (55109 ≤ n ∧ n ≤ 65535) ∨ (65537 ≤ n ∧ n ≤ 92681) ∨
  (92683 ≤ n ∧ n ≤ 262143) ∨ (262145 ≤ n ∧ n ≤ 311743) ∨
  311745 ≤ n

theorem odd_tail_interval_cover (n : ℕ) (hn : 2001 ≤ n) (ho : Odd n) : Route n := by
  obtain ⟨k, hk⟩ := ho
  unfold Route
  omega

end Sude

namespace Sude

/-- Transfer a strict power threshold from consecutive odd boundary values
    to every odd input, using monotonicity of natural-number powers. -/
theorem odd_power_boundary (n l p b : ℕ) (hn : Odd n) (hl : Odd l)
    (below : l ^ p < b) (above : b ≤ (l + 2) ^ p) :
    n ^ p < b ↔ n ≤ l := by
  obtain ⟨i, hi⟩ := hn
  obtain ⟨j, hj⟩ := hl
  constructor
  · intro h
    by_contra hnle
    have hge : l + 2 ≤ n := by omega
    have hpow := Nat.pow_le_pow_left hge p
    omega
  · intro h
    have hpow := Nat.pow_le_pow_left h p
    omega

end Sude

namespace Sude

theorem boundary_19483 (n : ℕ) (hn : Odd n) :
    n ^ 4 < 2 ^ 57 ↔ n ≤ 19483 := by
  apply odd_power_boundary n 19483 4 (2 ^ 57) hn <;> decide

theorem boundary_27553 (n : ℕ) (hn : Odd n) :
    n ^ 4 < 2 ^ 59 ↔ n ≤ 27553 := by
  apply odd_power_boundary n 27553 4 (2 ^ 59) hn <;> decide

theorem boundary_35733 (n : ℕ) (hn : Odd n) :
    n ^ 8 < 2 ^ 121 ↔ n ≤ 35733 := by
  apply odd_power_boundary n 35733 8 (2 ^ 121) hn <;> decide

theorem boundary_38967 (n : ℕ) (hn : Odd n) :
    n ^ 4 < 2 ^ 61 ↔ n ≤ 38967 := by
  apply odd_power_boundary n 38967 4 (2 ^ 61) hn <;> decide

theorem boundary_46339 (n : ℕ) (hn : Odd n) :
    n ^ 2 < 2 ^ 31 ↔ n ≤ 46339 := by
  apply odd_power_boundary n 46339 2 (2 ^ 31) hn <;> decide

theorem boundary_55107 (n : ℕ) (hn : Odd n) :
    n ^ 4 < 2 ^ 63 ↔ n ≤ 55107 := by
  apply odd_power_boundary n 55107 4 (2 ^ 63) hn <;> decide

theorem boundary_92681 (n : ℕ) (hn : Odd n) :
    n ^ 2 < 2 ^ 33 ↔ n ≤ 92681 := by
  apply odd_power_boundary n 92681 2 (2 ^ 33) hn <;> decide

theorem boundary_311743 (n : ℕ) (hn : Odd n) :
    n ^ 4 < 2 ^ 73 ↔ n ≤ 311743 := by
  apply odd_power_boundary n 311743 4 (2 ^ 73) hn <;> decide

end Sude

namespace Sude

/-- The predicates in T2001.1, excluding the ambient oddness hypothesis. -/
def SourceRoutes (n : ℕ) : Prop :=
  (2001 ≤ n ∧ n ≤ 19483) ∨
  (2^57 ≤ n^4 ∧ n^4 < 2^59) ∨
  (2^59 ≤ n^4 ∧ n^8 < 2^121) ∨
  (2^121 ≤ n^8 ∧ n^4 < 2^61) ∨
  (2^61 ≤ n^4 ∧ n^2 < 2^31) ∨
  (2^31 ≤ n^2 ∧ n^4 < 2^63) ∨
  (2^63 ≤ n^4 ∧ n < 2^16) ∨
  (2^16 ≤ n ∧ n^2 < 2^33) ∨
  (2^33 ≤ n^2 ∧ n < 2^18) ∨
  (2^18 ≤ n ∧ n^4 < 2^73) ∨
  311744 ≤ n

theorem source_routes_iff_interval_routes (n : ℕ) (hn : 2001 ≤ n) (ho : Odd n) :
    SourceRoutes n ↔ Route n := by
  have h1 := boundary_19483 n ho
  have h2 := boundary_27553 n ho
  have h3 := boundary_35733 n ho
  have h4 := boundary_38967 n ho
  have h5 := boundary_46339 n ho
  have h6 := boundary_55107 n ho
  have h7 := boundary_92681 n ho
  have h8 := boundary_311743 n ho
  obtain ⟨k, hk⟩ := ho
  unfold SourceRoutes Route
  omega

end Sude

namespace Sude

theorem odd_tail_source_cover (n : ℕ) (hn : 2001 ≤ n) (ho : Odd n) :
    SourceRoutes n :=
  (source_routes_iff_interval_routes n hn ho).mpr (odd_tail_interval_cover n hn ho)

end Sude
