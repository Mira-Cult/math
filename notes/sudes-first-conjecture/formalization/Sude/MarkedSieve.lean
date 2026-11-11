import Sude.SieveProgression

/-! A finite marking sieve over odd-indexed candidates. This specification
proves correctness; it does not assert large-prefix computational acceptance. -/
namespace Sude
noncomputable section

/-- Union the finite progressions for all odd base primes. -/
def compositeMarkIndices (base : Finset ℕ) (lo width : ℕ) : Finset ℕ :=
  (base.filter fun p => p % 2 = 1).biUnion (fun p => markingIndices p lo width)

/-- Unmarked indices in an odd-indexed half-open segment. -/
def unmarkedIndices (base : Finset ℕ) (lo width : ℕ) : Finset ℕ :=
  Finset.range width \ compositeMarkIndices base lo width

/-- The candidate passes the base-prime test exactly when it is not
marked by any odd base-prime progression. -/
theorem unmarkedIndices_spec (base : Finset ℕ) (lo width i : ℕ)
    (hbase : ∀ p ∈ base, Nat.Prime p) (hlo : 3 ≤ lo) (hodd : lo % 2 = 1) :
    i ∈ unmarkedIndices base lo width ↔
      i < width ∧ passesPrimeBase base (lo + 2 * i) = true := by
  classical
  have hvalodd : (lo + 2 * i) % 2 = 1 := by omega
  simp only [unmarkedIndices, Finset.mem_sdiff, Finset.mem_range,
    compositeMarkIndices, Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨hi, hnone⟩
    refine ⟨hi, ?_⟩
    simp only [passesPrimeBase, decide_eq_true_eq]
    refine ⟨by omega, ?_⟩
    intro p hp hsq hmod
    have hprime := hbase p hp
    rcases hprime.eq_two_or_odd with htwo | hpodd
    · subst p
      omega
    · have hmark : i ∈ markingIndices p lo width :=
        (markingIndices_spec p lo width i hprime.pos hpodd hodd).mpr
          ⟨hi, hsq, Nat.dvd_of_mod_eq_zero hmod⟩
      exact hnone ⟨p, ⟨hp, hpodd⟩, hmark⟩
  · rintro ⟨hi, hpass⟩
    refine ⟨hi, ?_⟩
    intro hsome
    obtain ⟨p, ⟨hp, hpodd⟩, hmark⟩ := hsome
    have hprime := hbase p hp
    have hmarks := (markingIndices_spec p lo width i hprime.pos hpodd hodd).mp hmark
    have htest : 2 ≤ lo + 2 * i ∧ ∀ q ∈ base,
        q * q ≤ lo + 2 * i → (lo + 2 * i) % q ≠ 0 := by
      exact of_decide_eq_true hpass
    exact (htest.2 p hp hmarks.2.1) (Nat.mod_eq_zero_of_dvd hmarks.2.2)

/-- Turn the unmarked indices into the corresponding odd values. -/
def markedSieveValues (base : Finset ℕ) (lo width : ℕ) : Finset ℕ :=
  (unmarkedIndices base lo width).image (fun i => lo + 2 * i)

/-- A finite progression-marking sieve returns exactly the odd primes in its
whole segment, provided the complete base covers the square-root domain. -/
theorem markedSieveValues_spec (base : Finset ℕ) (bound lo width : ℕ)
    (hbase : CompletePrimeBase base bound) (hlo : 3 ≤ lo) (hodd : lo % 2 = 1)
    (hbound : lo + 2 * width ≤ (bound + 1) * (bound + 1)) :
    markedSieveValues base lo width = oddPrimeSegment lo (lo + 2 * width) := by
  classical
  have hprimebase : ∀ p ∈ base, Nat.Prime p := fun p hp => ((hbase p).mp hp).1
  ext m
  simp only [markedSieveValues, Finset.mem_image, oddPrimeSegment, Finset.mem_filter,
    Finset.mem_Ico]
  constructor
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨hiwidth, hpass⟩ := (unmarkedIndices_spec base lo width i hprimebase hlo hodd).mp hi
    have hp := (passesPrimeBase_iff_prime base bound (lo + 2 * i) hbase (by omega)).mp hpass
    exact ⟨⟨by omega, by omega⟩, hp, by omega⟩
  · rintro ⟨⟨hmlo, hmhi⟩, hp, hne⟩
    have hmod : m % 2 = 1 := hp.eq_two_or_odd.resolve_left hne
    let i := (m - lo) / 2
    have hvalue : lo + 2 * i = m := by dsimp [i]; omega
    have hiwidth : i < width := by dsimp [i]; omega
    refine ⟨i, ?_, hvalue⟩
    apply (unmarkedIndices_spec base lo width i hprimebase hlo hodd).mpr
    refine ⟨hiwidth, ?_⟩
    apply (passesPrimeBase_iff_prime base bound (lo + 2 * i) hbase (by omega)).mpr
    simpa [hvalue] using hp

end
end Sude
