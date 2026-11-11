import Sude.PrimeSegmentSieve
import Mathlib.Algebra.Order.Floor.Div

/-! The odd-multiple marking progression used by a segmented sieve. This
module proves arithmetic coverage; no tail-sized sieve acceptance follows. -/
namespace Sude
noncomputable section

/-- The least odd natural at or above k. -/
def oddCeiling (k : ℕ) : ℕ := if k % 2 = 1 then k else k + 1

theorem oddCeiling_spec (k : ℕ) :
    k ≤ oddCeiling k ∧ oddCeiling k % 2 = 1 ∧
      ∀ j, k ≤ j → j % 2 = 1 → oddCeiling k ≤ j := by
  have hm := Nat.mod_lt k (by decide : 0 < 2)
  by_cases h : k % 2 = 1
  · simp only [oddCeiling, h, if_true]
    exact ⟨le_rfl, trivial, fun _ hj _ => hj⟩
  · have hz : k % 2 = 0 := by omega
    simp only [oddCeiling, h, if_false]
    refine ⟨by omega, by omega, ?_⟩
    intro j hj hjodd
    omega

/-- First odd multiple of p at or beyond both lo and p². The quotient is
rounded upward, then advanced once if it is even. -/
def firstOddMark (p lo : ℕ) : ℕ := p * oddCeiling (max p (lo ⌈/⌉ p))

/-- This quotient formulation is exactly the source rule: start at
max(p², ceil(lo/p)*p), then add p when that multiple is even. -/
theorem firstOddMark_source_formula (p lo : ℕ) (hodd : p % 2 = 1) :
    firstOddMark p lo =
      let first := max (p * p) ((lo ⌈/⌉ p) * p)
      if first % 2 = 0 then first + p else first := by
  let q := lo ⌈/⌉ p
  let k := max p q
  have hm : max (p * p) (q * p) = p * k := by
    dsimp [k]
    rw [mul_max]
    simp [Nat.mul_comm]
  change p * oddCeiling k =
    if (max (p * p) (q * p)) % 2 = 0 then max (p * p) (q * p) + p
    else max (p * p) (q * p)
  rw [hm]
  have hkbound := Nat.mod_lt k (by decide : 0 < 2)
  by_cases hk : k % 2 = 1
  · simp [oddCeiling, hk, Nat.mul_mod, hodd]
  · have hk0 : k % 2 = 0 := by omega
    simp [oddCeiling, hk0, Nat.mul_mod, hodd, Nat.mul_add]

/-- The first mark is odd, divisible by p, and past both lower bounds. -/
theorem firstOddMark_properties (p lo : ℕ) (hp : 0 < p) (hodd : p % 2 = 1) :
    lo ≤ firstOddMark p lo ∧ p * p ≤ firstOddMark p lo ∧
      p ∣ firstOddMark p lo ∧ firstOddMark p lo % 2 = 1 := by
  let k := max p (lo ⌈/⌉ p)
  have hk₁ : p ≤ k := le_max_left _ _
  have hk₂ : lo ⌈/⌉ p ≤ k := le_max_right _ _
  have hoddK := oddCeiling_spec k
  have hlo : lo ≤ p * (lo ⌈/⌉ p) := (ceilDiv_le_iff_le_mul hp).1 (le_refl _)
  have hA : lo ≤ p * oddCeiling k :=
    hlo.trans (Nat.mul_le_mul_left p (hk₂.trans hoddK.1))
  have hB : p * p ≤ p * oddCeiling k := Nat.mul_le_mul_left p (hk₁.trans hoddK.1)
  refine ⟨hA, hB, ⟨oddCeiling k, rfl⟩, ?_⟩
  change (p * oddCeiling k) % 2 = 1
  simp [Nat.mul_mod, hodd, hoddK.2.1]

/-- Any eligible odd multiple has a quotient at least the selected odd
ceiling. This includes candidates exactly at lo or p². -/
theorem firstOddMark_quotient_le (p lo j : ℕ) (hp : 0 < p) (hodd : p % 2 = 1)
    (hjodd : (p * j) % 2 = 1) (hlo : lo ≤ p * j) (hsq : p * p ≤ p * j) :
    oddCeiling (max p (lo ⌈/⌉ p)) ≤ j := by
  have hjmod : j % 2 = 1 := by
    have hh : (p % 2 * (j % 2)) % 2 = 1 := by simpa [Nat.mul_mod] using hjodd
    simpa [hodd] using hh
  have hpj : p ≤ j := Nat.le_of_mul_le_mul_left hsq hp
  have hcj : lo ⌈/⌉ p ≤ j := (ceilDiv_le_iff_le_mul hp).2 hlo
  exact (oddCeiling_spec _).2.2 j (max_le hpj hcj) hjmod

/-- Exactly the eligible odd multiples occur in the progression from the
first mark with step 2p. This is independent of any segment representation. -/
theorem firstOddMark_progression (p lo m : ℕ) (hp : 0 < p) (hodd : p % 2 = 1) :
    (m % 2 = 1 ∧ lo ≤ m ∧ p * p ≤ m ∧ p ∣ m) ↔
      ∃ t : ℕ, m = firstOddMark p lo + (2 * p) * t := by
  constructor
  · rintro ⟨hm, hlo, hsq, hdiv⟩
    obtain ⟨j, rfl⟩ := hdiv
    let k := oddCeiling (max p (lo ⌈/⌉ p))
    have hkj : k ≤ j := firstOddMark_quotient_le p lo j hp hodd hm hlo hsq
    have hjodd : j % 2 = 1 := by
      have hh : (p % 2 * (j % 2)) % 2 = 1 := by simpa [Nat.mul_mod] using hm
      simpa [hodd] using hh
    have hkodd : k % 2 = 1 := (oddCeiling_spec _).2.1
    have hj : j = k + 2 * ((j - k) / 2) := by omega
    refine ⟨(j - k) / 2, ?_⟩
    change p * j = p * k + (2 * p) * ((j - k) / 2)
    calc
      p * j = p * (k + 2 * ((j - k) / 2)) := congrArg (p * ·) hj
      _ = _ := by ring
  · rintro ⟨t, rfl⟩
    obtain ⟨hlo, hsq, hdiv, hfirstOdd⟩ := firstOddMark_properties p lo hp hodd
    refine ⟨?_, by omega, by omega, ?_⟩
    · simp [Nat.add_mod, Nat.mul_mod, hfirstOdd]
    · exact dvd_add hdiv (dvd_mul_of_dvd_left (dvd_mul_left p 2) t)

/-- Odd candidates in a segment are `lo + 2*i`. This is the index of the
first marked candidate when the lower endpoint is odd. -/
def firstMarkIndex (p lo : ℕ) : ℕ := (firstOddMark p lo - lo) / 2

/-- The number of marked indices below the segment width. -/
def markingCount (p lo width : ℕ) : ℕ :=
  if firstMarkIndex p lo < width then (width - 1 - firstMarkIndex p lo) / p + 1 else 0

/-- The actual finite marking progression in index space; no trial
division is performed on nonmultiples. -/
def markingIndices (p lo width : ℕ) : Finset ℕ :=
  (Finset.range (markingCount p lo width)).image (fun t => firstMarkIndex p lo + p * t)

/-- The recorded index maps exactly to the first marked odd value. -/
theorem firstMarkIndex_value (p lo : ℕ) (hp : 0 < p)
    (hpodd : p % 2 = 1) (hloodd : lo % 2 = 1) :
    lo + 2 * firstMarkIndex p lo = firstOddMark p lo := by
  have ⟨hlo, _, _, hmarkodd⟩ := firstOddMark_properties p lo hp hpodd
  unfold firstMarkIndex
  omega

/-- The finite progression length is exact, including an empty segment and
a first mark at the last allowed index. -/
theorem markingCount_spec (p lo width t : ℕ) (hp : 0 < p) :
    t < markingCount p lo width ↔ firstMarkIndex p lo + p * t < width := by
  unfold markingCount
  by_cases hfirst : firstMarkIndex p lo < width
  · simp only [hfirst, if_true]
    have hdiv := (Nat.le_div_iff_mul_le hp :
      t ≤ (width - 1 - firstMarkIndex p lo) / p ↔
        t * p ≤ width - 1 - firstMarkIndex p lo)
    rw [Nat.mul_comm t p] at hdiv
    omega
  · simp only [hfirst, if_false, Nat.not_lt_zero, false_iff]
    omega

/-- An index is marked exactly when its odd candidate is divisible by p
and is at least p². -/
theorem markingIndices_spec (p lo width i : ℕ) (hp : 0 < p)
    (hpodd : p % 2 = 1) (hloodd : lo % 2 = 1) :
    i ∈ markingIndices p lo width ↔
      i < width ∧ p * p ≤ lo + 2 * i ∧ p ∣ lo + 2 * i := by
  have hstart := firstMarkIndex_value p lo hp hpodd hloodd
  have hvalueOdd : (lo + 2 * i) % 2 = 1 := by omega
  constructor
  · intro hi
    obtain ⟨t, ht, hti⟩ := Finset.mem_image.mp hi
    have htwidth := (markingCount_spec p lo width t hp).mp (Finset.mem_range.mp ht)
    have hvalue : lo + 2 * i = firstOddMark p lo + (2 * p) * t := by
      rw [← hti, ← hstart]
      ring
    have hmarks := (firstOddMark_progression p lo (lo + 2 * i) hp hpodd).mpr ⟨t, hvalue⟩
    exact ⟨hti ▸ htwidth, hmarks.2.2.1, hmarks.2.2.2⟩
  · rintro ⟨hi, hsq, hdiv⟩
    obtain ⟨t, ht⟩ := (firstOddMark_progression p lo (lo + 2 * i) hp hpodd).mp
      ⟨hvalueOdd, by omega, hsq, hdiv⟩
    have hti : firstMarkIndex p lo + p * t = i := by
      rw [← hstart] at ht
      nlinarith
    apply Finset.mem_image.mpr
    refine ⟨t, Finset.mem_range.mpr ((markingCount_spec p lo width t hp).mpr ?_), hti⟩
    simpa [hti] using hi

end
end Sude
