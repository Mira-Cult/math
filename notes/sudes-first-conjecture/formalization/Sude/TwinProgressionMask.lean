import Sude.BitsetSieve
import Mathlib.Algebra.Ring.GeomSum

/-! A geometric-series representation of the bit masks used by the finite
  twin scan. The equivalence with the current sieve is a separate obligation. -/
namespace Sude
noncomputable section

/-- The binary integer whose intended set bits are `first + p * t` for
`0 ≤ t < count`. Positive `p` is required for that interpretation. -/
def geometricProgressionMask (p first count : ℕ) : ℕ :=
  2 ^ first * ((2 ^ (p * count) - 1) / (2 ^ p - 1))

/-- Geometric mask is the ordinary natural-number sum of the indicated powers
of two. This also holds for the empty progression. -/
theorem geometricProgressionMask_eq_sum {p : ℕ} (hp : 0 < p) (first count : ℕ) :
    geometricProgressionMask p first count =
      ∑ t ∈ Finset.range count, 2 ^ (first + p * t) := by
  have hp2 : 2 ≤ 2 ^ p := Nat.one_lt_pow (by omega) (by decide)
  unfold geometricProgressionMask
  rw [show 2 ^ (p * count) = (2 ^ p) ^ count by rw [pow_mul]]
  rw [← Nat.geomSum_eq hp2]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [pow_add, pow_mul]

private lemma geopow_bound (p : ℕ) (hp : 0 < p) (n : ℕ) :
    (∑ t ∈ Finset.range n, 2^(p*t)) < 2^(p*n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hp' : p*n + 1 ≤ p*(n+1) := by simp only [Nat.mul_add, Nat.mul_one]; omega
    have hpow : 2^(p*n+1) ≤ 2^(p*(n+1)) := Nat.pow_le_pow_right (by decide) hp'
    have h2 : (2:ℕ)^(p*n+1) = 2^(p*n)+2^(p*n) := by simp [pow_succ, Nat.mul_comm, Nat.two_mul]
    omega

private lemma geopow_bits (p : ℕ) (hp : 0 < p) (n i : ℕ) :
    (∑ t ∈ Finset.range n, 2^(p*t)).testBit i = true ↔ ∃ t < n, i = p*t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hbound := geopow_bound p hp n
    have heq : (∑ t ∈ Finset.range n, 2^(p*t)) + 2^(p*n) =
        (∑ t ∈ Finset.range n, 2^(p*t)) ||| 2^(p*n) := by
      rw [Nat.lor_comm, Nat.add_comm]
      simpa using Nat.two_pow_add_eq_or_of_lt hbound 1
    rw [heq, Nat.testBit_lor, Bool.or_eq_true, ih, Nat.testBit_two_pow]
    simp only [decide_eq_true_eq]
    constructor
    · rintro (⟨t, ht, he⟩ | he)
      · exact ⟨t, by omega, he⟩
      · exact ⟨n, by omega, he.symm⟩
    · rintro ⟨t, ht, he⟩
      by_cases htn : t = n
      · right; subst t; exact he.symm
      · left; exact ⟨t, by omega, he⟩

/-- For positive spacing the quotient-based mask sets precisely the desired
progression bits, including the zero-count case. -/
theorem geometricProgressionMask_testBit {p : ℕ} (hp : 0 < p)
    (first count i : ℕ) :
    (geometricProgressionMask p first count).testBit i = true ↔
      ∃ t < count, i = first + p * t := by
  rw [geometricProgressionMask_eq_sum hp first count]
  have hshift : (∑ t ∈ Finset.range count, 2 ^ (first + p * t)) =
      (∑ t ∈ Finset.range count, 2 ^ (p * t)) <<< first := by
    rw [Nat.shiftLeft_eq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t ht
    rw [pow_add, Nat.mul_comm]
  rw [hshift, Nat.testBit_shiftLeft]
  simp only [Bool.and_eq_true, decide_eq_true_eq, geopow_bits p hp]
  constructor
  · rintro ⟨h, t, ht, he⟩
    exact ⟨t, ht, by omega⟩
  · rintro ⟨t, ht, he⟩
    exact ⟨by omega, t, ht, by omega⟩

/-- The quotient mask is exactly the existing individual-bit encoding for
one positive-step marking progression. -/
theorem geometricProgressionMask_eq_encode {p : ℕ} (hp : 0 < p)
    (first count : ℕ) :
    geometricProgressionMask p first count =
      encodeMarkBits ((List.range count).map (fun t => first + p * t)) := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  rw [geometricProgressionMask_testBit hp, encodeMarkBits_spec]
  simp [eq_comm]

/-- Short-circuit empty and singleton progressions so a large step does not
force a large power merely to encode zero or one bit. -/
def fastProgressionMask (p first count : ℕ) : ℕ :=
  match count with
  | 0 => 0
  | 1 => 2 ^ first
  | k + 2 => geometricProgressionMask p first (k + 2)

theorem fastProgressionMask_eq {p : ℕ} (hp : 0 < p) (first count : ℕ) :
    fastProgressionMask p first count = geometricProgressionMask p first count := by
  cases count with
  | zero => simp [fastProgressionMask, geometricProgressionMask]
  | succ count =>
    cases count with
    | zero =>
      have hp2 : 1 < 2 ^ p := Nat.one_lt_pow (by omega) (by decide)
      have hpos : 0 < 2 ^ p - 1 := by omega
      simp [fastProgressionMask, geometricProgressionMask, Nat.div_self hpos]
    | succ count => rfl

/-- Alternative per-prime marking implementation. It has the same odd-base
filter as `markingIndexList`. No performance claim is made. -/
def geometricSegmentMarkBits (base : List ℕ) (lo width : ℕ) : ℕ :=
  (base.filter fun p => p % 2 = 1).foldr
    (fun p bits => fastProgressionMask p (firstMarkIndex p lo) (markingCount p lo width) ||| bits) 0

private theorem encodeMarkBits_append (xs ys : List ℕ) :
    encodeMarkBits (xs ++ ys) = encodeMarkBits xs ||| encodeMarkBits ys := by
  induction xs with
  | nil => simp [encodeMarkBits]
  | cons x xs ih => simp [encodeMarkBits, ih, Nat.lor_assoc]

/-- Folding geometric masks over the actual base computes the very same bit
integer as the existing list-of-individual-marks implementation. The result
holds for arbitrary bases, lower endpoints, and widths, including zero width;
the original odd filter excludes zero as a step. -/
theorem geometricSegmentMarkBits_eq (base : List ℕ) (lo width : ℕ) :
    geometricSegmentMarkBits base lo width = segmentMarkBits base lo width := by
  have hfold : ∀ ps : List ℕ, (∀ p ∈ ps, 0 < p) →
      ps.foldr (fun p bits => fastProgressionMask p (firstMarkIndex p lo) (markingCount p lo width) ||| bits) 0 =
        encodeMarkBits (ps.flatMap fun p =>
          (List.range (markingCount p lo width)).map (fun t => firstMarkIndex p lo + p * t)) := by
    intro ps hp
    induction ps with
    | nil => simp [encodeMarkBits]
    | cons p ps ih =>
      have hp0 : 0 < p := hp p (by simp)
      have hps : ∀ q ∈ ps, 0 < q := by
        intro q hq
        exact hp q (by simp [hq])
      simp only [List.foldr_cons, List.flatMap_cons, encodeMarkBits_append]
      rw [fastProgressionMask_eq hp0, geometricProgressionMask_eq_encode hp0, ih hps]
  apply hfold
  intro p hp
  simp only [List.mem_filter, decide_eq_true_eq] at hp
  omega

end
end Sude
