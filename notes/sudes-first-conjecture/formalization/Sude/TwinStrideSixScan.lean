import Sude.TwinGeometricScan

/-! A bounded stride-six twin-pair checker. This prototype reuses the
existing odd-position marking mask, then checks only the possible lower
endpoints `lo + 6*i`. No performance claim or large scan is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096

/-- Stream only bits numbered 3i and 3i+1 of an odd-candidate marking mask.
Those are the two endpoints of the pair with lower endpoint `lo + 6i`. -/
def strideSixTwinCount : ℕ → ℕ → ℕ
  | _, 0 => 0
  | bits, width + 1 =>
      let rest := strideSixTwinCount (bits / 8) width
      if bits.testBit 0 = false ∧ bits.testBit 1 = false then rest + 1 else rest

/-- The stride-six streaming count counts exactly the intended indexed bits,
including the lookahead bit at the upper endpoint of the last pair. -/
theorem strideSixTwinCount_spec (bits width : ℕ) :
    strideSixTwinCount bits width =
      ∑ i ∈ Finset.range width,
        if bits.testBit (3 * i) = false ∧ bits.testBit (3 * i + 1) = false then 1 else 0 := by
  induction width generalizing bits with
  | zero => simp [strideSixTwinCount]
  | succ width ih =>
    rw [Finset.sum_range_succ']
    simp only [strideSixTwinCount, ih]
    have hbit (i : ℕ) : (bits / 8).testBit i = bits.testBit (i + 3) := by
      simpa using (Nat.testBit_div_two_pow (n := 3) bits i)
    simp only [hbit]
    have heq (i : ℕ) : 3 * (i + 1) = 3 * i + 3 := by omega
    simp only [heq]
    split_ifs <;> simp_all [Nat.add_left_comm, Nat.add_comm]

/-- Reuse the verified geometric marking mask; only the final counting step
is stride-six. The mask itself still covers every odd position. -/
def strideSixGeometricTwinScan (base : List ℕ) (lo width : ℕ) : ℕ :=
  strideSixTwinCount
    (geometricSegmentMarkBits (activeMarkingBase base lo (3 * width + 1)) lo (3 * width + 1)) width

/-- Every twin-prime lower endpoint greater than 3 is 5 modulo 6. -/
theorem twinPrime_lower_mod_six (p : ℕ) (hp : Nat.Prime p) (hp2 : Nat.Prime (p + 2))
    (hlo : 3 < p) : p % 6 = 5 := by
  have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have hp3 : p % 3 ≠ 0 := by
    intro h
    have hd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
    have heq := (Nat.dvd_prime_two_le hp (by decide : 2 ≤ 3)).mp hd
    omega
  have hp23 : (p + 2) % 3 ≠ 0 := by
    intro h
    have hd : 3 ∣ p + 2 := Nat.dvd_of_mod_eq_zero h
    have heq := (Nat.dvd_prime_two_le hp2 (by decide : 2 ≤ 3)).mp hd
    omega
  have hsum : (p + 2) % 3 = (p % 3 + 2) % 3 := by simp [Nat.add_mod]
  have hpmod : p % 3 = 2 := by
    have hr := Nat.mod_lt p (by decide : 0 < 3)
    interval_cases hrem : p % 3 <;> simp_all
  omega

/-- The set of stride-six indices passing the verified prime sieve. -/
def strideSixTwinIndices (base : List ℕ) (lo width : ℕ) : Finset ℕ :=
  let bits := geometricSegmentMarkBits (activeMarkingBase base lo (3 * width + 1)) lo (3 * width + 1)
  (Finset.range width).filter fun i => bits.testBit (3 * i) = false ∧ bits.testBit (3 * i + 1) = false

/-- The bounded counter and the corresponding finite index set agree. -/
theorem strideSixGeometricTwinScan_card (base : List ℕ) (lo width : ℕ) :
    strideSixGeometricTwinScan base lo width = (strideSixTwinIndices base lo width).card := by
  rw [strideSixGeometricTwinScan, strideSixTwinCount_spec, strideSixTwinIndices, Finset.card_filter]

/-- For a 5-mod-6 lower boundary, the stride-six scan counts exactly the
mathematical half-open twin-prime segment. The lookahead requirement covers
the second endpoint of every counted pair. -/
theorem strideSixGeometricTwinScan_spec (base : List ℕ) (bound lo width : ℕ)
    (hbase : CompletePrimeBase base.toFinset bound) (hlo : 5 ≤ lo) (hmod : lo % 6 = 5)
    (hbound : lo + 2 * (3 * width + 1) ≤ (bound + 1) * (bound + 1)) :
    strideSixGeometricTwinScan base lo width = (twinPrimeSegment lo (lo + 6 * width)).card := by
  classical
  have hodd : lo % 2 = 1 := by omega
  have hbits : geometricSegmentMarkBits (activeMarkingBase base lo (3 * width + 1)) lo (3 * width + 1) =
      segmentMarkBits base lo (3 * width + 1) := by
    rw [geometricSegmentMarkBits_eq, activeMarkingBase_bits_eq]
  have hindex : ∀ i < width, i ∈ strideSixTwinIndices base lo width ↔
      Nat.Prime (lo + 6 * i) ∧ Nat.Prime (lo + 6 * i + 2) := by
    intro i hi
    simp only [strideSixTwinIndices, Finset.mem_filter, Finset.mem_range, hbits]
    rw [segment_clear_iff_prime base bound lo (3 * width + 1) (3 * i) hbase (by omega) hodd (by omega) hbound,
      segment_clear_iff_prime base bound lo (3 * width + 1) (3 * i + 1) hbase (by omega) hodd (by omega) hbound]
    have heq0 : lo + 2 * (3 * i) = lo + 6 * i := by omega
    have heq1 : lo + 2 * (3 * i + 1) = lo + 6 * i + 2 := by omega
    rw [heq0, heq1]
    simp [hi]
  have hinj : Function.Injective (fun i : ℕ => lo + 6 * i) := by
    intro i j h
    dsimp only at h
    omega
  rw [strideSixGeometricTwinScan_card, ← Finset.card_image_of_injective _ hinj]
  congr 1
  ext p
  simp only [Finset.mem_image, twinPrimeSegment, Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hi' : i < width := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hp := (hindex i hi').mp hi
    exact ⟨⟨by omega, by omega⟩, hp.1, hp.2, by omega⟩
  · rintro ⟨⟨hl, hh⟩, hp, hp2, _⟩
    have hpmod := twinPrime_lower_mod_six p hp hp2 (by omega)
    let i := (p - lo) / 6
    have hi : i < width := by dsimp [i]; omega
    have heq : lo + 6 * i = p := by dsimp [i]; omega
    exact ⟨i, (hindex i hi).mpr (by simpa [heq] using And.intro hp hp2), heq⟩

/-- First integer at or above `lo` that is 5 modulo 6. -/
def strideSixFirst (lo : ℕ) : ℕ := lo + (5 - lo % 6)

/-- Number of such integers strictly below `hi`. This is zero when the
aligned start is at or beyond the half-open upper boundary. -/
def strideSixWidth (lo hi : ℕ) : ℕ := (hi - strideSixFirst lo + 5) / 6

/-- General half-open interval checker. It reads the final partner even
when that partner lies at or above `hi`. -/
def strideSixIntervalScan (base : List ℕ) (lo hi : ℕ) : ℕ :=
  strideSixGeometricTwinScan base (strideSixFirst lo) (strideSixWidth lo hi)

/-- The arbitrary-boundary wrapper gives the exact mathematical segment
count, including empty intervals and an upper endpoint crossing. -/
theorem strideSixIntervalScan_spec (base : List ℕ) (bound lo hi : ℕ)
    (hbase : CompletePrimeBase base.toFinset bound) (hlo : 5 ≤ lo)
    (hbound : strideSixFirst lo + 2 * (3 * strideSixWidth lo hi + 1) ≤
      (bound + 1) * (bound + 1)) :
    strideSixIntervalScan base lo hi = (twinPrimeSegment lo hi).card := by
  have hfirstLo : lo ≤ strideSixFirst lo := by simp [strideSixFirst]
  have hfirstHi : strideSixFirst lo ≤ lo + 5 := by unfold strideSixFirst; omega
  have hfirstMod : strideSixFirst lo % 6 = 5 := by
    unfold strideSixFirst
    have h := Nat.mod_lt lo (by decide : 0 < 6)
    omega
  have hfirst5 : 5 ≤ strideSixFirst lo := by omega
  rw [strideSixIntervalScan, strideSixGeometricTwinScan_spec base bound _ _ hbase hfirst5 hfirstMod hbound]
  congr 1
  ext p
  simp only [twinPrimeSegment, Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨hpLo, hpHi⟩, hp, hp2, hodd⟩
    have hpmod := twinPrime_lower_mod_six p hp hp2 (by omega)
    have hw := Nat.div_add_mod (hi - strideSixFirst lo + 5) 6
    have hwmod := Nat.mod_lt (hi - strideSixFirst lo + 5) (by decide : 0 < 6)
    unfold strideSixWidth at hpHi
    exact ⟨⟨by omega, by omega⟩, hp, hp2, hodd⟩
  · rintro ⟨⟨hpLo, hpHi⟩, hp, hp2, hodd⟩
    have hpmod := twinPrime_lower_mod_six p hp hp2 (by omega)
    have hw := Nat.div_add_mod (hi - strideSixFirst lo + 5) 6
    have hwmod := Nat.mod_lt (hi - strideSixFirst lo + 5) (by decide : 0 < 6)
    unfold strideSixWidth
    exact ⟨⟨by omega, by omega⟩, hp, hp2, hodd⟩

/-- The last lower endpoint 59 is counted although its partner 61 lies
beyond the half-open upper boundary 60. -/
theorem strideSixBoundaryExample_checked :
    strideSixIntervalScan (canonicalPrimeBaseList 11) 45 60 = 1 := by
  decide +kernel

theorem strideSixBoundaryExample_mathematical : (twinPrimeSegment 45 60).card = 1 := by
  have h := strideSixIntervalScan_spec (canonicalPrimeBaseList 11) 11 45 60
    (canonicalPrimeBaseList_complete 11) (by decide) (by decide)
  rw [strideSixBoundaryExample_checked] at h
  exact h.symm

end
end Sude
