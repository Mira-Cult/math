import Sude.TwinStrideSixScan
import Mathlib.Tactic.IntervalCases

/-! Compressed stride-six marking progressions. This source is a correctness
prototype; no large acceptance or performance claim is made. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- First old odd-progression step which reaches an index divisible by 3. -/
def strideSixFirstStep (p first : ℕ) : ℕ := ((3 - first % 3) * (p % 3)) % 3

/-- A nonzero residue modulo 3 is its own inverse. -/
theorem strideSixFirstStep_spec (p first t : ℕ) (hp3 : p % 3 ≠ 0) :
    (first + p * t) % 3 = 0 ↔ t % 3 = strideSixFirstStep p first := by
  have hp := Nat.mod_lt p (by decide : 0 < 3)
  have hf := Nat.mod_lt first (by decide : 0 < 3)
  have ht := Nat.mod_lt t (by decide : 0 < 3)
  have hmod : (first + p * t) % 3 = (first % 3 + (p % 3) * (t % 3)) % 3 := by
    simp [Nat.add_mod, Nat.mul_mod]
  rw [hmod]
  unfold strideSixFirstStep
  interval_cases hpm : p % 3 <;> interval_cases hfm : first % 3 <;>
    interval_cases htm : t % 3 <;> simp_all

/-- Compress an odd-index marking progression to the indices 0 mod 3.
This is purely arithmetic and preserves the first-mark position. -/
theorem strideSixProgression_spec (p first i : ℕ) (hp3 : p % 3 ≠ 0) :
    (∃ t, 3 * i = first + p * t) ↔
      ∃ j, i = (first + p * strideSixFirstStep p first) / 3 + p * j := by
  let t0 := strideSixFirstStep p first
  have ht0 : t0 < 3 := Nat.mod_lt _ (by decide)
  have hfirst : (first + p * t0) % 3 = 0 := by
    apply (strideSixFirstStep_spec p first t0 hp3).mpr
    exact Nat.mod_eq_of_lt ht0
  have hfirstDiv : 3 * ((first + p * t0) / 3) = first + p * t0 := by
    have hd := Nat.div_add_mod (first + p * t0) 3
    omega
  constructor
  · rintro ⟨t, ht⟩
    have htmod : t % 3 = t0 := by
      apply (strideSixFirstStep_spec p first t hp3).mp
      rw [← ht]
      omega
    have hteq : t = t0 + 3 * (t / 3) := by
      have hd := Nat.div_add_mod t 3
      omega
    refine ⟨t / 3, ?_⟩
    have hmul : p * t = p * t0 + 3 * (p * (t / 3)) := by
      calc
        p * t = p * (t0 + 3 * (t / 3)) := congrArg (fun x => p * x) hteq
        _ = p * t0 + 3 * (p * (t / 3)) := by ring
    rw [hmul] at ht
    change i = (first + p * t0) / 3 + p * (t / 3)
    omega
  · rintro ⟨j, hj⟩
    refine ⟨t0 + 3 * j, ?_⟩
    rw [hj, Nat.mul_add, hfirstDiv]
    ring

/-- First compressed index in a prime's stride-six lane. -/
def strideSixLaneFirst (p lo : ℕ) : ℕ :=
  let first := firstMarkIndex p lo
  (first + p * strideSixFirstStep p first) / 3

/-- Number of in-range terms in the compressed marking progression. -/
def strideSixLaneCount (p first width : ℕ) : ℕ :=
  if first < width then (width - 1 - first) / p + 1 else 0

theorem strideSixLaneCount_spec (p first width t : ℕ) (hp : 0 < p) :
    t < strideSixLaneCount p first width ↔ first + p * t < width := by
  unfold strideSixLaneCount
  by_cases hfirst : first < width
  · simp only [hfirst, if_true]
    have hdiv := (Nat.le_div_iff_mul_le hp :
      t ≤ (width - 1 - first) / p ↔ t * p ≤ width - 1 - first)
    rw [Nat.mul_comm t p] at hdiv
    omega
  · simp only [hfirst, if_false, Nat.not_lt_zero, false_iff]
    omega

/-- One short bit-mask marks exactly the 0-mod-3 entries of the former
odd-indexed marking progression. -/
def strideSixLanePrimeMask (p lo width : ℕ) : ℕ :=
  fastProgressionMask p (strideSixLaneFirst p lo)
    (strideSixLaneCount p (strideSixLaneFirst p lo) width)

theorem strideSixLanePrimeMask_spec (p lo width i : ℕ) (hp : 0 < p) (hp3 : p % 3 ≠ 0) :
    (strideSixLanePrimeMask p lo width).testBit i = true ↔
      3 * i ∈ markingIndices p lo (3 * width) := by
  rw [strideSixLanePrimeMask, fastProgressionMask_eq hp, geometricProgressionMask_testBit hp]
  simp only [markingIndices, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨t, ht, rfl⟩
    have htwidth := (strideSixLaneCount_spec p _ width t hp).mp ht
    have hprogress : ∃ k, 3 * (strideSixLaneFirst p lo + p * t) = firstMarkIndex p lo + p * k :=
      (strideSixProgression_spec p (firstMarkIndex p lo) _ hp3).mpr ⟨t, rfl⟩
    obtain ⟨k, hk⟩ := hprogress
    refine ⟨k, (markingCount_spec p lo (3 * width) k hp).mpr ?_, hk.symm⟩
    rw [← hk]
    omega
  · rintro ⟨t, ht, heq⟩
    have hlt := (markingCount_spec p lo (3 * width) t hp).mp ht
    have hprogress : ∃ j, i = strideSixLaneFirst p lo + p * j :=
      (strideSixProgression_spec p (firstMarkIndex p lo) i hp3).mp ⟨t, heq.symm⟩
    obtain ⟨j, hj⟩ := hprogress
    refine ⟨j, (strideSixLaneCount_spec p _ width j hp).mpr ?_, hj⟩
    rw [heq] at hlt
    omega

/-- Fold the compressed progression masks for the applicable odd primes.
The exceptional primes 2 and 3 are excluded from these two residue lanes. -/
def strideSixLaneMask (base : List ℕ) (lo width : ℕ) : ℕ :=
  base.foldr (fun p bits =>
    if p % 2 = 1 ∧ p % 3 ≠ 0 then strideSixLanePrimeMask p lo width ||| bits else bits) 0

theorem strideSixLaneMask_spec (base : List ℕ) (lo width i : ℕ) :
    (strideSixLaneMask base lo width).testBit i = true ↔
      ∃ p ∈ base, p % 2 = 1 ∧ p % 3 ≠ 0 ∧ 3 * i ∈ markingIndices p lo (3 * width) := by
  induction base with
  | nil => simp [strideSixLaneMask]
  | cons p ps ih =>
    change (if p % 2 = 1 ∧ p % 3 ≠ 0 then
      strideSixLanePrimeMask p lo width ||| strideSixLaneMask ps lo width
      else strideSixLaneMask ps lo width).testBit i = true ↔ _
    by_cases hp : p % 2 = 1 ∧ p % 3 ≠ 0
    · have hp0 : 0 < p := by omega
      rw [if_pos hp, Nat.testBit_lor, Bool.or_eq_true,
        strideSixLanePrimeMask_spec p lo width i hp0 hp.2, ih]
      constructor
      · rintro (hmark | ⟨q, hq, hqodd, hq3, hqmark⟩)
        · exact ⟨p, by simp, hp.1, hp.2, hmark⟩
        · exact ⟨q, by simp [hq], hqodd, hq3, hqmark⟩
      · rintro ⟨q, hq, hqodd, hq3, hqmark⟩
        rcases List.mem_cons.mp hq with rfl | hq
        · exact Or.inl hqmark
        · exact Or.inr ⟨q, hq, hqodd, hq3, hqmark⟩
    · simp only [hp, if_false, ih]
      constructor
      · rintro ⟨q, hq, hqodd, hq3, hqmark⟩
        exact ⟨q, by simp [hq], hqodd, hq3, hqmark⟩
      · rintro ⟨q, hq, hqodd, hq3, hqmark⟩
        rcases List.mem_cons.mp hq with rfl | hq
        · exact False.elim (hp ⟨hqodd, hq3⟩)
        · exact ⟨q, hq, hqodd, hq3, hqmark⟩

/-- For a lane not divisible by 3, its compressed bits are exactly the old
odd-position mask sampled every third bit. -/
theorem strideSixLaneMask_eq_old (base : List ℕ) (lo width i : ℕ)
    (hprime : ∀ p ∈ base, Nat.Prime p) (hodd : lo % 2 = 1) (hlo3 : lo % 3 ≠ 0) :
    (strideSixLaneMask base lo width).testBit i =
      (segmentMarkBits base lo (3 * width)).testBit (3 * i) := by
  apply Bool.eq_iff_iff.mpr
  rw [strideSixLaneMask_spec, segmentMarkBits_spec]
  simp only [compositeMarkIndices, Finset.mem_biUnion, Finset.mem_filter, List.mem_toFinset]
  constructor
  · rintro ⟨p, hp, hpodd, _, hmark⟩
    exact ⟨p, ⟨hp, hpodd⟩, hmark⟩
  · rintro ⟨p, ⟨hp, hpodd⟩, hmark⟩
    have hp3 : p % 3 ≠ 0 := by
      intro hdiv
      have hpdvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero hdiv
      have heq := (Nat.dvd_prime_two_le (hprime p hp) (by decide : 2 ≤ 3)).mp hpdvd
      subst p
      have hmark' := (markingIndices_spec 3 lo (3 * width) (3 * i) (by decide) (by decide) hodd).mp hmark
      have hdiv' := Nat.mod_eq_zero_of_dvd hmark'.2.2
      omega
    exact ⟨p, hp, hpodd, hp3, hmark⟩

/-- Stream zero bits in a compressed pair mask. -/
def strideSixClearCount : ℕ → ℕ → ℕ
  | _, 0 => 0
  | bits, width + 1 =>
      let rest := strideSixClearCount (bits / 2) width
      if bits.testBit 0 = false then rest + 1 else rest

theorem strideSixClearCount_spec (bits width : ℕ) :
    strideSixClearCount bits width =
      ∑ i ∈ Finset.range width, if bits.testBit i = false then 1 else 0 := by
  induction width generalizing bits with
  | zero => simp [strideSixClearCount]
  | succ width ih =>
    rw [Finset.sum_range_succ']
    simp only [strideSixClearCount, ih, Nat.testBit_succ]
    split_ifs <;> simp_all [Nat.add_comm]

/-- Each bit marks either a composite lower candidate or its +2 partner.
Both lane masks have one bit per 6-step candidate, rather than three odd
candidate positions. -/
def strideSixCompressedTwinScan (base : List ℕ) (lo width : ℕ) : ℕ :=
  strideSixClearCount (strideSixLaneMask base lo width |||
    strideSixLaneMask base (lo + 2) width) width

/-- Compressed two-lane scanning equals the existing verified stride-six
baseline under the same complete-base and endpoint bound. -/
theorem strideSixCompressedTwinScan_eq (base : List ℕ) (bound lo width : ℕ)
    (hbase : CompletePrimeBase base.toFinset bound) (hlo : 5 ≤ lo) (hmod : lo % 6 = 5)
    (hbound : lo + 2 * (3 * width + 1) ≤ (bound + 1) * (bound + 1)) :
    strideSixCompressedTwinScan base lo width = strideSixGeometricTwinScan base lo width := by
  have hprime : ∀ p ∈ base, Nat.Prime p := by
    intro p hp
    exact ((hbase p).mp (List.mem_toFinset.mpr hp)).1
  have hodd : lo % 2 = 1 := by omega
  have hlo3 : lo % 3 ≠ 0 := by omega
  have hodd2 : (lo + 2) % 2 = 1 := by omega
  have hlo32 : (lo + 2) % 3 ≠ 0 := by omega
  have hbits : geometricSegmentMarkBits (activeMarkingBase base lo (3 * width + 1)) lo (3 * width + 1) =
      segmentMarkBits base lo (3 * width + 1) := by
    rw [geometricSegmentMarkBits_eq, activeMarkingBase_bits_eq]
  rw [strideSixCompressedTwinScan, strideSixClearCount_spec,
    strideSixGeometricTwinScan, strideSixTwinCount_spec, hbits]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < width := Finset.mem_range.mp hi
  have hloBound : lo + 2 * (3 * width) ≤ (bound + 1) * (bound + 1) := by omega
  have hhiBound : lo + 2 + 2 * (3 * width) ≤ (bound + 1) * (bound + 1) := by omega
  have hp0 := segment_clear_iff_prime base bound lo (3 * width) (3 * i)
    hbase (by omega) hodd (by omega) hloBound
  have hp1 := segment_clear_iff_prime base bound (lo + 2) (3 * width) (3 * i)
    hbase (by omega) hodd2 (by omega) hhiBound
  have hp0' := segment_clear_iff_prime base bound lo (3 * width + 1) (3 * i)
    hbase (by omega) hodd (by omega) hbound
  have hp1' := segment_clear_iff_prime base bound lo (3 * width + 1) (3 * i + 1)
    hbase (by omega) hodd (by omega) hbound
  have heq0 : lo + 2 * (3 * i) = lo + 6 * i := by omega
  have heq1 : (lo + 2) + 2 * (3 * i) = lo + 2 * (3 * i + 1) := by omega
  rw [heq1] at hp1
  rw [Nat.testBit_lor, strideSixLaneMask_eq_old base lo width i hprime hodd hlo3,
    strideSixLaneMask_eq_old base (lo + 2) width i hprime hodd2 hlo32]
  have hc : ((segmentMarkBits base lo (3 * width)).testBit (3 * i) ||
      (segmentMarkBits base (lo + 2) (3 * width)).testBit (3 * i)) = false ↔
      (segmentMarkBits base lo (3 * width + 1)).testBit (3 * i) = false ∧
      (segmentMarkBits base lo (3 * width + 1)).testBit (3 * i + 1) = false := by
    simp only [Bool.or_eq_false_iff]
    exact ⟨fun ⟨ha, hb⟩ => ⟨hp0'.mpr (hp0.mp ha), hp1'.mpr (hp1.mp hb)⟩,
      fun ⟨ha, hb⟩ => ⟨hp0.mpr (hp0'.mp ha), hp1.mpr (hp1'.mp hb)⟩⟩
  exact if_congr hc rfl rfl

/-- Exact mathematical count on an aligned half-open interval. -/
theorem strideSixCompressedTwinScan_spec (base : List ℕ) (bound lo width : ℕ)
    (hbase : CompletePrimeBase base.toFinset bound) (hlo : 5 ≤ lo) (hmod : lo % 6 = 5)
    (hbound : lo + 2 * (3 * width + 1) ≤ (bound + 1) * (bound + 1)) :
    strideSixCompressedTwinScan base lo width = (twinPrimeSegment lo (lo + 6 * width)).card := by
  rw [strideSixCompressedTwinScan_eq base bound lo width hbase hlo hmod hbound,
    strideSixGeometricTwinScan_spec base bound lo width hbase hlo hmod hbound]

/-- Arbitrary half-open lower-endpoint interval, aligned internally to the
first possible twin-prime residue. -/
def strideSixCompressedIntervalScan (base : List ℕ) (lo hi : ℕ) : ℕ :=
  strideSixCompressedTwinScan base (strideSixFirst lo) (strideSixWidth lo hi)

/-- The compressed checker agrees with the existing mathematical segment
count for arbitrary endpoints, including an empty interval or a pair crossing
its upper boundary. -/
theorem strideSixCompressedIntervalScan_spec (base : List ℕ) (bound lo hi : ℕ)
    (hbase : CompletePrimeBase base.toFinset bound) (hlo : 5 ≤ lo)
    (hbound : strideSixFirst lo + 2 * (3 * strideSixWidth lo hi + 1) ≤
      (bound + 1) * (bound + 1)) :
    strideSixCompressedIntervalScan base lo hi = (twinPrimeSegment lo hi).card := by
  have hfirst : 5 ≤ strideSixFirst lo := by unfold strideSixFirst; omega
  have hmod : strideSixFirst lo % 6 = 5 := by
    unfold strideSixFirst
    have h := Nat.mod_lt lo (by decide : 0 < 6)
    omega
  rw [strideSixCompressedIntervalScan,
    strideSixCompressedTwinScan_eq base bound _ _ hbase hfirst hmod hbound]
  exact strideSixIntervalScan_spec base bound lo hi hbase hlo hbound

/-- The compressed checker counts the lower endpoint 59 even though its
partner 61 lies beyond the half-open upper boundary 60. -/
theorem strideSixCompressedBoundary_checked :
    strideSixCompressedIntervalScan (canonicalPrimeBaseList 11) 45 60 = 1 := by
  decide +kernel

theorem strideSixCompressedBoundary_mathematical : (twinPrimeSegment 45 60).card = 1 := by
  have h := strideSixCompressedIntervalScan_spec (canonicalPrimeBaseList 11) 11 45 60
    (canonicalPrimeBaseList_complete 11) (by decide) (by decide)
  rw [strideSixCompressedBoundary_checked] at h
  exact h.symm

end
end Sude
