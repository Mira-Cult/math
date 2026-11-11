import Sude.FiniteTwinOddBaseComplete
import Sude.TwinStrideSixCompressed

/-! Fast single-pass stride-six twin-prime segment scanner and its equivalence
to the mathematical `twinPrimeSegment` count. -/
namespace Sude
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- Direct arithmetic computation of `strideSixLaneFirst` avoiding typeclass projections. -/
def fastStrideSixLaneFirst (p lo : ℕ) : ℕ :=
  let q := (lo + p - 1) / p
  let m := if p ≤ q then q else p
  let k := if m % 2 = 1 then m else m + 1
  let firstOdd := (p * k - lo) / 2
  let step := ((3 - firstOdd % 3) * (p % 3)) % 3
  (firstOdd + p * step) / 3

theorem fastStrideSixLaneFirst_eq (p lo : ℕ) :
    fastStrideSixLaneFirst p lo = strideSixLaneFirst p lo := by
  simp only [fastStrideSixLaneFirst, strideSixLaneFirst, firstMarkIndex, firstOddMark,
    oddCeiling, max_def, Nat.ceilDiv_eq_add_pred_div, strideSixFirstStep]

/-- Single-lane compressed marking mask using `fastStrideSixLaneFirst`. -/
def fastLanePrimeMask (p lo width : ℕ) : ℕ :=
  let first := fastStrideSixLaneFirst p lo
  if first < width then
    fastProgressionMask p first ((width - 1 - first) / p + 1)
  else 0

theorem fastLanePrimeMask_eq (p lo width : ℕ) :
    fastLanePrimeMask p lo width = strideSixLanePrimeMask p lo width := by
  unfold fastLanePrimeMask strideSixLanePrimeMask strideSixLaneCount
  rw [fastStrideSixLaneFirst_eq]
  by_cases h : strideSixLaneFirst p lo < width <;> simp [h, fastProgressionMask]

/-- Single-pass fold accumulating both the `lo` and `lo + 2` stride-six lane masks. -/
def fastListBothLanesMask (base : List ℕ) (lo width : ℕ) : ℕ :=
  base.foldr (fun p bits =>
    (fastLanePrimeMask p lo width ||| fastLanePrimeMask p (lo + 2) width) ||| bits) 0

theorem fastListBothLanesMask_eq (base : List ℕ) (lo width : ℕ)
    (hbase : ∀ p ∈ base, p % 2 = 1 ∧ p % 3 ≠ 0) :
    fastListBothLanesMask base lo width =
      strideSixLaneMask base lo width ||| strideSixLaneMask base (lo + 2) width := by
  induction base with
  | nil => simp [fastListBothLanesMask, strideSixLaneMask]
  | cons p ps ih =>
    have hp : p % 2 = 1 ∧ p % 3 ≠ 0 := hbase p List.mem_cons_self
    have hps : ∀ q ∈ ps, q % 2 = 1 ∧ q % 3 ≠ 0 :=
      fun q hq => hbase q (List.mem_cons_of_mem p hq)
    change (fastLanePrimeMask p lo width ||| fastLanePrimeMask p (lo + 2) width) |||
      fastListBothLanesMask ps lo width =
      (if p % 2 = 1 ∧ p % 3 ≠ 0 then
        strideSixLanePrimeMask p lo width ||| strideSixLaneMask ps lo width
       else strideSixLaneMask ps lo width) |||
      (if p % 2 = 1 ∧ p % 3 ≠ 0 then
        strideSixLanePrimeMask p (lo + 2) width ||| strideSixLaneMask ps (lo + 2) width
       else strideSixLaneMask ps (lo + 2) width)
    rw [if_pos hp, if_pos hp, ih hps, fastLanePrimeMask_eq, fastLanePrimeMask_eq]
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_lor, Bool.or_assoc, Bool.or_left_comm]

theorem finiteTwinOddBase_head_eq :
    finiteTwinOddBase = 3 :: finiteTwinOddBase.tail := rfl

theorem finiteTwinOddBase_tail_all :
    finiteTwinOddBase.tail.all (fun p => decide (p % 2 = 1 ∧ p % 3 ≠ 0)) = true := by
  decide +kernel

theorem finiteTwinOddBase_tail_valid (p : ℕ) (hp : p ∈ finiteTwinOddBase.tail) :
    p % 2 = 1 ∧ p % 3 ≠ 0 := by
  have hall := List.all_eq_true.mp finiteTwinOddBase_tail_all p hp
  exact of_decide_eq_true hall

/-- Fast combined lane mask over `finiteTwinOddBase.tail`. -/
def fastTailBothLanesMask (lo width : ℕ) : ℕ :=
  fastListBothLanesMask finiteTwinOddBase.tail lo width

theorem strideSixLaneMask_checked_eq_tail (lo width : ℕ) :
    strideSixLaneMask finiteTwinCheckedBase lo width =
      strideSixLaneMask finiteTwinOddBase.tail lo width := by
  rw [finiteTwinCheckedBase, finiteTwinOddBase_head_eq]
  simp [strideSixLaneMask]

theorem fastTailBothLanesMask_eq (lo width : ℕ) :
    fastTailBothLanesMask lo width =
      strideSixLaneMask finiteTwinCheckedBase lo width |||
        strideSixLaneMask finiteTwinCheckedBase (lo + 2) width := by
  rw [fastTailBothLanesMask,
    fastListBothLanesMask_eq finiteTwinOddBase.tail lo width finiteTwinOddBase_tail_valid,
    strideSixLaneMask_checked_eq_tail lo width,
    strideSixLaneMask_checked_eq_tail (lo + 2) width]

/-- 8-bit SWAR popcount. -/
def popcount8 (x : ℕ) : ℕ :=
  let x1 := x - ((x >>> 1) &&& 0x55)
  let x2 := (x1 &&& 0x33) + ((x1 >>> 2) &&& 0x33)
  (x2 + (x2 >>> 4)) &&& 0x0f

theorem popcount8_fin :
    ∀ x : Fin 256,
      popcount8 x.val = ∑ i ∈ Finset.range 8, if x.val.testBit i = true then 1 else 0 := by
  decide +kernel

theorem popcount8_spec (bits : ℕ) :
    popcount8 (bits &&& 0xff) =
      ∑ i ∈ Finset.range 8, if bits.testBit i = true then 1 else 0 := by
  have hlt : bits &&& 0xff < 256 := by
    change bits &&& (2 ^ 8 - 1) < 256
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt bits (by decide)
  have hfin := popcount8_fin ⟨bits &&& 0xff, hlt⟩
  dsimp at hfin
  rw [hfin]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i < 8 := Finset.mem_range.mp hi
  have htb : (bits &&& 0xff).testBit i = bits.testBit i := by
    change (bits &&& (2 ^ 8 - 1)).testBit i = bits.testBit i
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.testBit_mod_two_pow]
    simp [hi']
  rw [htb]

/-- Divide-and-conquer popcount over `8 * 2^d` bits with zero-branch pruning. -/
def fastSetCount : ℕ → ℕ → ℕ
  | 0, bits => popcount8 (bits &&& 0xff)
  | d + 1, bits =>
      if bits = 0 then 0
      else
        let half := 8 <<< d
        fastSetCount d (bits &&& ((1 <<< half) - 1)) + fastSetCount d (bits >>> half)

theorem fastSetCount_spec (d bits : ℕ) :
    fastSetCount d bits =
      ∑ i ∈ Finset.range (8 <<< d), if bits.testBit i = true then 1 else 0 := by
  induction d generalizing bits with
  | zero =>
    simpa [fastSetCount] using popcount8_spec bits
  | succ d ih =>
    unfold fastSetCount
    split_ifs with h0
    · subst h0
      simp
    · have hshift : 8 <<< (d + 1) = (8 <<< d) + (8 <<< d) := by
        simp only [Nat.shiftLeft_eq, pow_succ]
        ring
      dsimp only
      rw [ih, ih, hshift, Finset.sum_range_add]
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        have hi' : i < 8 <<< d := Finset.mem_range.mp hi
        have hmask : (bits &&& ((1 <<< (8 <<< d)) - 1)).testBit i = bits.testBit i := by
          rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, Nat.testBit_mod_two_pow]
          simp [hi']
        rw [hmask]
      · apply Finset.sum_congr rfl
        intro i _
        have hshr : (bits >>> (8 <<< d)).testBit i = bits.testBit (8 <<< d + i) := by
          rw [Nat.testBit_shiftRight, Nat.add_comm]
        rw [hshr]

theorem strideSixLaneMask_testBit_of_le (base : List ℕ) (lo width i : ℕ) (hi : width ≤ i) :
    (strideSixLaneMask base lo width).testBit i = false := by
  by_contra h
  have htrue : (strideSixLaneMask base lo width).testBit i = true := by
    cases htb : (strideSixLaneMask base lo width).testBit i
    · exact False.elim (h htb)
    · rfl
  obtain ⟨p, _, hpodd, _, hmark⟩ := (strideSixLaneMask_spec base lo width i).mp htrue
  have hp0 : 0 < p := by omega
  obtain ⟨t, ht, hti⟩ := Finset.mem_image.mp hmark
  have hlt := (markingCount_spec p lo (3 * width) t hp0).mp (Finset.mem_range.mp ht)
  omega

theorem fastSetCount_eq_sub_clearCount (d : ℕ) (base : List ℕ) (lo width : ℕ)
    (hw : width ≤ 8 <<< d) :
    width - fastSetCount d (strideSixLaneMask base lo width |||
      strideSixLaneMask base (lo + 2) width) =
      strideSixClearCount (strideSixLaneMask base lo width |||
        strideSixLaneMask base (lo + 2) width) width := by
  let bits := strideSixLaneMask base lo width ||| strideSixLaneMask base (lo + 2) width
  change width - fastSetCount d bits = strideSixClearCount bits width
  rw [fastSetCount_spec, strideSixClearCount_spec]
  have hsplit : Finset.range (8 <<< d) =
      Finset.range width ∪ Finset.Ico width (8 <<< d) := by
    ext i
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  have hdisj : Disjoint (Finset.range width) (Finset.Ico width (8 <<< d)) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    simp only [Finset.mem_range, Finset.mem_Ico] at hi1 hi2
    omega
  have hhigh : ∑ i ∈ Finset.Ico width (8 <<< d), (if bits.testBit i = true then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hwi : width ≤ i := (Finset.mem_Ico.mp hi).1
    have htb : bits.testBit i = false := by
      simp only [bits, Nat.testBit_lor,
        strideSixLaneMask_testBit_of_le base lo width i hwi,
        strideSixLaneMask_testBit_of_le base (lo + 2) width i hwi, Bool.or_self]
    simp [htb]
  rw [hsplit, Finset.sum_union hdisj, hhigh, add_zero]
  have hsum :
      (∑ i ∈ Finset.range width, if bits.testBit i = true then 1 else 0) +
      (∑ i ∈ Finset.range width, if bits.testBit i = false then 1 else 0) = width := by
    rw [← Finset.sum_add_distrib]
    have h1 : ∀ i ∈ Finset.range width,
        (if bits.testBit i = true then 1 else 0) +
        (if bits.testBit i = false then 1 else 0) = 1 := by
      intro i _
      cases bits.testBit i <;> rfl
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  omega

/-- Fast single-pass interval scan for segments of stride-six width at most `2^19 = 524,288`. -/
def fastStrideSixIntervalScan (lo hi : ℕ) : ℕ :=
  let first := strideSixFirst lo
  let width := strideSixWidth lo hi
  width - fastSetCount 16 (fastTailBothLanesMask first width)

/-- Exact mathematical specification of `fastStrideSixIntervalScan`. -/
theorem fastStrideSixIntervalScan_spec (lo hi : ℕ)
    (hlo : 5 ≤ lo) (hw : strideSixWidth lo hi ≤ 524288)
    (hlook : strideSixFirst lo + 2 * (3 * strideSixWidth lo hi + 1) ≤ 32769 * 32769) :
    fastStrideSixIntervalScan lo hi = (twinPrimeSegment lo hi).card := by
  unfold fastStrideSixIntervalScan
  dsimp only
  rw [fastTailBothLanesMask_eq,
    fastSetCount_eq_sub_clearCount 16 finiteTwinCheckedBase (strideSixFirst lo)
      (strideSixWidth lo hi) (by simpa using hw)]
  change strideSixCompressedIntervalScan finiteTwinCheckedBase lo hi = (twinPrimeSegment lo hi).card
  exact strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 lo hi
    finiteTwinCheckedBase_complete hlo hlook

end
end Sude
