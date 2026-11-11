import Sude.FiniteTwinSeed
import Sude.FWActualSeed

/-! Exact interface from the FT scan to FW's actual-pool matching. -/
namespace Sude
noncomputable section

/-- A fully accepted FT scan would provide precisely the finite population
and prime-domain facts consumed by FW. Acceptance remains an explicit
internal obligation and is not an imported theorem. -/
theorem finiteTwinSeeds_source_data_of_scan
    (hscan : twinBitsetCountScan (canonicalPrimeBaseList 32768) 45 finiteTwinSeedWidths = 3650551) :
    3650551 ≤ finiteTwinSeeds.card ∧
      (∀ p ∈ finiteTwinSeeds, p + 2 ≤ 2 ^ 30) ∧
      (∀ p ∈ finiteTwinSeeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2)) := by
  refine ⟨(finiteTwinSeeds_count_of_scan hscan).ge, ?_, ?_⟩
  · intro p hp
    exact ((mem_finiteTwinSeeds p).mp hp).2.2.2
  · intro p hp
    obtain ⟨hlo, hp0, hp1, _⟩ := (mem_finiteTwinSeeds p).mp hp
    exact ⟨hlo, hp0, hp1⟩

/-- After acceptance of the complete FT scan, the FW candidate quota is
selected from the source's exact set of twin primes in the prescribed pool. -/
theorem fw_candidates_of_finiteTwin_scan (lower : RSIndexLower) (n : ℕ)
    (bridges : Finset ℕ) (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (hbridge : ∀ p ∈ bridges, poolMaximum n ≤ 4 * p)
    (hscan : twinBitsetCountScan (canonicalPrimeBaseList 32768) 45 finiteTwinSeedWidths = 3650551) :
    ∃ candidates : Finset ℕ,
      candidates ⊆ finiteTwinSeeds ∧ candidates.card = 6 * (n + 8) * (16 + 2 - 1) ∧
      PairwiseDisjointPairs candidates 2 ∧
      pairFootprint candidates 2 ⊆ poolFinset n \ bridges ∧
      (pairFootprint candidates 2).card = 2 * (6 * (n + 8) * (16 + 2 - 1)) := by
  obtain ⟨hcount, hseed, hprime⟩ := finiteTwinSeeds_source_data_of_scan hscan
  exact fw_actual_seed_candidates_after_bridges lower n finiteTwinSeeds bridges hnlo hnhi
    hseed hprime hbridge hcount

end
end Sude
