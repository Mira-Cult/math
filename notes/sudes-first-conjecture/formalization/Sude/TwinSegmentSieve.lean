import Sude.BitsetSieve

/-! A gap-two segment sieve with explicit one-candidate lookahead. -/
namespace Sude
noncomputable section

/-- Lower endpoints of genuine odd gap-two prime pairs in a half-open
interval. The upper endpoint may lie in the following segment. -/
def twinPrimeSegment (lo hi : ℕ) : Finset ℕ :=
  (Finset.Ico lo hi).filter fun p => Nat.Prime p ∧ Nat.Prime (p + 2) ∧ p % 2 = 1

/-- Mark one extra odd candidate so the final lower endpoint is tested
against its partner across the boundary. -/
def twinBitsetIndices (base : List ℕ) (lo width : ℕ) : Finset ℕ :=
  let bits := segmentMarkBits base lo (width + 1)
  (Finset.range width).filter fun i => bits.testBit i = false ∧ bits.testBit (i + 1) = false

/-- Enumerated lower endpoints returned by the lookahead sieve. -/
def twinBitsetLowers (base : List ℕ) (lo width : ℕ) : Finset ℕ :=
  (twinBitsetIndices base lo width).image fun i => lo + 2 * i

/-- For any in-range odd candidate, a clear bit is equivalent to actual
primality under the complete base-prime and square-root hypotheses. -/
theorem segment_clear_iff_prime (base : List ℕ) (bound lo width i : ℕ)
    (hbase : CompletePrimeBase base.toFinset bound) (hlo : 3 ≤ lo)
    (hodd : lo % 2 = 1) (hi : i < width)
    (hbound : lo + 2 * width ≤ (bound + 1) * (bound + 1)) :
    (segmentMarkBits base lo width).testBit i = false ↔ Nat.Prime (lo + 2 * i) := by
  have hprimebase : ∀ p ∈ base.toFinset, Nat.Prime p := fun p hp => ((hbase p).mp hp).1
  have hclear : (segmentMarkBits base lo width).testBit i = false ↔
      i ∈ bitsetUnmarked base lo width := by simp [bitsetUnmarked, hi]
  rw [hclear, bitsetUnmarked_eq, unmarkedIndices_spec base.toFinset lo width i hprimebase hlo hodd]
  rw [passesPrimeBase_iff_prime base.toFinset bound (lo + 2 * i) hbase (by omega)]
  simp [hi]

/-- The lookahead checker returns exactly the mathematical gap-two prime
pairs whose lower endpoints lie in the segment, including a boundary pair. -/
theorem twinBitsetLowers_spec (base : List ℕ) (bound lo width : ℕ)
    (hbase : CompletePrimeBase base.toFinset bound) (hlo : 3 ≤ lo)
    (hodd : lo % 2 = 1)
    (hbound : lo + 2 * (width + 1) ≤ (bound + 1) * (bound + 1)) :
    twinBitsetLowers base lo width = twinPrimeSegment lo (lo + 2 * width) := by
  classical
  have hindex : ∀ i < width, i ∈ twinBitsetIndices base lo width ↔
      Nat.Prime (lo + 2 * i) ∧ Nat.Prime (lo + 2 * i + 2) := by
    intro i hi
    simp only [twinBitsetIndices, Finset.mem_filter, Finset.mem_range]
    rw [segment_clear_iff_prime base bound lo (width + 1) i hbase hlo hodd (by omega) hbound,
      segment_clear_iff_prime base bound lo (width + 1) (i + 1) hbase hlo hodd (by omega) hbound]
    have heq : lo + 2 * (i + 1) = lo + 2 * i + 2 := by omega
    rw [heq]
    simp [hi]
  ext p
  simp only [twinBitsetLowers, Finset.mem_image, twinPrimeSegment, Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hirange : i < width := (Finset.mem_filter.mp hi).1 |> Finset.mem_range.mp
    have hp := (hindex i hirange).mp hi
    exact ⟨⟨by omega, by omega⟩, hp.1, hp.2, by omega⟩
  · rintro ⟨⟨hlo', hhi'⟩, hp, hp2, hmod⟩
    let i := (p - lo) / 2
    have hi : i < width := by dsimp [i]; omega
    have heq : lo + 2 * i = p := by dsimp [i]; omega
    refine ⟨i, (hindex i hi).mpr ?_, heq⟩
    simpa [heq] using And.intro hp hp2

end
end Sude
