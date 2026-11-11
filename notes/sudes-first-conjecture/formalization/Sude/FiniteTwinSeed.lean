import Sude.TwinSegmentScan
import Sude.PrimePairMatching

/-! Exact FT finite matching proposition and a kernel-checked boundary case. -/
namespace Sude
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The source's complete set of lower endpoints, with `p > 43` and
`p + 2 ≤ 2^30`. -/
def finiteTwinSeeds : Finset ℕ := twinPrimeSegment 45 (2 ^ 30 - 1)

theorem mem_finiteTwinSeeds (p : ℕ) : p ∈ finiteTwinSeeds ↔
    43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2) ∧ p + 2 ≤ 2 ^ 30 := by
  simp only [finiteTwinSeeds, twinPrimeSegment, Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hp, hp2, hodd⟩
    exact ⟨by omega, hp, hp2, by omega⟩
  · rintro ⟨hlo, hp, hp2, hhi⟩
    have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
    exact ⟨⟨by omega, by omega⟩, hp, hp2, hodd⟩

/-- The finite twin-prime set is a vertex-disjoint matching, independently
of any numerical population claim. -/
theorem finiteTwinSeeds_matching : PairwiseDisjointPairs finiteTwinSeeds 2 := by
  apply binary_prime_family_disjoint finiteTwinSeeds 1
  intro p hp
  obtain ⟨hlo, hp0, hp1, _⟩ := (mem_finiteTwinSeeds p).mp hp
  simpa using (show 3 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2) from ⟨by omega, hp0, hp1⟩)

/-- The actual 512-segment lower-endpoint plan. The final segment is one
candidate shorter than the source's prime scan because it uses lookahead. -/
def finiteTwinSeedWidths : List ℕ := List.replicate 511 (2 ^ 20) ++ [1048553]

theorem finiteTwinSeedWidths_sum : finiteTwinSeedWidths.sum = 536870889 := by
  decide +kernel

/-- If every segment of this explicit plan is kernel-accepted, the result is
the exact source population. This theorem does not assert acceptance. -/
theorem finiteTwinSeeds_count_of_scan
    (hscan : twinBitsetCountScan (canonicalPrimeBaseList 32768) 45 finiteTwinSeedWidths = 3650551) :
    finiteTwinSeeds.card = 3650551 := by
  have h := twinBitsetCountScan_spec (canonicalPrimeBaseList 32768) 32768 45 finiteTwinSeedWidths
    (canonicalPrimeBaseList_complete 32768) (by decide) (by decide)
    (by rw [finiteTwinSeedWidths_sum]; decide)
  rw [hscan, finiteTwinSeedWidths_sum] at h
  have hend : 45 + 2 * 536870889 = 2 ^ 30 - 1 := by decide
  simpa [finiteTwinSeeds, hend] using h.symm

/-- A kernel-checked segment whose only twin pair crosses the segment
boundary: the lower endpoint 59 is inside and 61 is the lookahead. -/
theorem twinBoundaryExample_checked :
    twinBitsetLowers (canonicalPrimeBaseList 9) 45 8 = {59} := by
  decide +kernel

theorem twinBoundaryExample_mathematical : twinPrimeSegment 45 61 = {59} := by
  have h := twinBitsetLowers_spec (canonicalPrimeBaseList 9) 9 45 8
    (canonicalPrimeBaseList_complete 9) (by decide) (by decide) (by decide)
  rw [twinBoundaryExample_checked] at h
  simpa using h.symm

end
end Sude
