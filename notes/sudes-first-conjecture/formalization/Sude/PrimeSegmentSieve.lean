import Sude.PrefixCount

/-! A finite prime-base segment checker. Soundness is proved below; no large
prefix or tail-table acceptance is assumed by this module. -/
namespace Sude
noncomputable section

/-- The base contains exactly the primes no greater than the bound. -/
def CompletePrimeBase (base : Finset ℕ) (bound : ℕ) : Prop :=
  ∀ q, q ∈ base ↔ Nat.Prime q ∧ q ≤ bound

/-- Canonical finite base; a faster proved base generator can replace it. -/
def canonicalPrimeBase (bound : ℕ) : Finset ℕ :=
  (Finset.range (bound + 1)).filter Nat.Prime

theorem canonicalPrimeBase_complete (bound : ℕ) :
    CompletePrimeBase (canonicalPrimeBase bound) bound := by
  intro q
  simp [canonicalPrimeBase, and_comm]

/-- Test a candidate by bounded trial division against a supplied base. -/
def passesPrimeBase (base : Finset ℕ) (m : ℕ) : Bool :=
  decide (2 ≤ m ∧ ∀ q ∈ base, q * q ≤ m → m % q ≠ 0)

/-- For m below the square of bound+1, the bounded test is exact. The
finite base's completeness is an explicit, checkable hypothesis. -/
theorem passesPrimeBase_iff_prime (base : Finset ℕ) (bound m : ℕ)
    (hbase : CompletePrimeBase base bound) (hbound : m < (bound + 1) * (bound + 1)) :
    passesPrimeBase base m = true ↔ Nat.Prime m := by
  simp only [passesPrimeBase, decide_eq_true_eq]
  constructor
  · rintro ⟨hm, htest⟩
    by_contra hnot
    let q := Nat.minFac m
    have hqprime : Nat.Prime q := Nat.minFac_prime (by omega)
    have hqSq : q * q ≤ m := by
      simpa only [q, pow_two] using Nat.minFac_sq_le_self (by omega : 0 < m) hnot
    have hqSqrt : q ≤ Nat.sqrt m := Nat.le_sqrt.mpr hqSq
    have hSqrt : Nat.sqrt m ≤ bound := by
      have hh : Nat.sqrt m < bound + 1 := Nat.sqrt_lt.mpr hbound
      omega
    have hqbase : q ∈ base := (hbase q).2 ⟨hqprime, hqSqrt.trans hSqrt⟩
    have hqdiv : q ∣ m := Nat.minFac_dvd m
    exact (htest q hqbase hqSq) (Nat.mod_eq_zero_of_dvd hqdiv)
  · intro hp
    refine ⟨hp.two_le, ?_⟩
    intro q hq hqSq hmod
    have hqprime := ((hbase q).1 hq).1
    have hqSqrt : q ≤ Nat.sqrt m := Nat.le_sqrt.mpr hqSq
    have hndiv := (Nat.prime_def_le_sqrt.mp hp).2 q hqprime.two_le hqSqrt
    exact hndiv (Nat.dvd_of_mod_eq_zero hmod)

/-- Candidate segment, using half-open endpoints and excluding 2. -/
def checkedOddSegment (base : Finset ℕ) (lo hi : ℕ) : Finset ℕ :=
  (Finset.Ico lo hi).filter fun m => m % 2 = 1 ∧ passesPrimeBase base m = true

/-- Mathematical odd-prime segment, independent of the checker. -/
def oddPrimeSegment (lo hi : ℕ) : Finset ℕ :=
  (Finset.Ico lo hi).filter fun m => Nat.Prime m ∧ m ≠ 2

/-- Adjacent half-open checker segments have no duplicated candidates. -/
theorem checkedOddSegment_disjoint (base : Finset ℕ) (lo mid hi : ℕ) :
    Disjoint (checkedOddSegment base lo mid) (checkedOddSegment base mid hi) := by
  apply Finset.disjoint_left.mpr
  intro m hleft hright
  simp only [checkedOddSegment, Finset.mem_filter, Finset.mem_Ico] at hleft hright
  omega

/-- Adjacent segments combine without gaps, retaining the same exact test. -/
theorem checkedOddSegment_union (base : Finset ℕ) {lo mid hi : ℕ}
    (hlm : lo ≤ mid) (hmh : mid ≤ hi) :
    checkedOddSegment base lo mid ∪ checkedOddSegment base mid hi =
      checkedOddSegment base lo hi := by
  ext m
  simp only [checkedOddSegment, Finset.mem_union, Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro (⟨⟨hlo, hmid⟩, hodd, hpass⟩ | ⟨⟨hmid, hhi⟩, hodd, hpass⟩)
    · exact ⟨⟨hlo, by omega⟩, hodd, hpass⟩
    · exact ⟨⟨by omega, hhi⟩, hodd, hpass⟩
  · rintro ⟨⟨hlo, hhi⟩, hodd, hpass⟩
    by_cases hm : m < mid
    · exact Or.inl ⟨⟨hlo, hm⟩, hodd, hpass⟩
    · exact Or.inr ⟨⟨by omega, hhi⟩, hodd, hpass⟩

/-- Counts and sums can be accumulated segment by segment. -/
theorem checkedOddSegment_additive (base : Finset ℕ) {lo mid hi : ℕ}
    (hlm : lo ≤ mid) (hmh : mid ≤ hi) :
    (checkedOddSegment base lo hi).card =
      (checkedOddSegment base lo mid).card + (checkedOddSegment base mid hi).card ∧
    (∑ p ∈ checkedOddSegment base lo hi, p) =
      (∑ p ∈ checkedOddSegment base lo mid, p) +
      (∑ p ∈ checkedOddSegment base mid hi, p) := by
  rw [← checkedOddSegment_union base hlm hmh,
    Finset.card_union_of_disjoint (checkedOddSegment_disjoint base lo mid hi),
    Finset.sum_union (checkedOddSegment_disjoint base lo mid hi)]
  exact ⟨rfl, rfl⟩

/-- Every checked segment equals the true odd-prime segment within the
base's proved square-root domain. -/
theorem checkedOddSegment_spec (base : Finset ℕ) (bound lo hi : ℕ)
    (hbase : CompletePrimeBase base bound) (hhi : hi ≤ (bound + 1) * (bound + 1)) :
    checkedOddSegment base lo hi = oddPrimeSegment lo hi := by
  ext m
  simp only [checkedOddSegment, oddPrimeSegment, Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨hlo, hmh⟩, hodd, hpass⟩
    have hp := (passesPrimeBase_iff_prime base bound m hbase (by omega)).mp hpass
    refine ⟨⟨hlo, hmh⟩, hp, ?_⟩
    omega
  · rintro ⟨⟨hlo, hmh⟩, hp, hne⟩
    have hodd := hp.eq_two_or_odd.resolve_left hne
    exact ⟨⟨hlo, hmh⟩, hodd,
      (passesPrimeBase_iff_prime base bound m hbase (by omega)).mpr hp⟩

/-- The mathematical segment from zero through X is precisely the prefix. -/
theorem oddPrimeSegment_zero (X : ℕ) :
    oddPrimeSegment 0 (X + 1) = oddPrimePrefix X := by
  ext p
  simp [oddPrimeSegment, oddPrimePrefix]

/-- A verified full segment gives both exact odd-prefix count and sum. -/
theorem checkedOddSegment_prefix (base : Finset ℕ) (bound X : ℕ)
    (hbase : CompletePrimeBase base bound) (hX : X + 1 ≤ (bound + 1) * (bound + 1)) :
    checkedOddSegment base 0 (X + 1) = oddPrimePrefix X :=
  (checkedOddSegment_spec base bound 0 (X + 1) hbase hX).trans (oddPrimeSegment_zero X)

end
end Sude
