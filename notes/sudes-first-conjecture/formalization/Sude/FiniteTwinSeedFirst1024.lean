import Sude.FiniteTwinSeed

/-! Kernel-accepted initial portion of the FT finite matching. -/
namespace Sude
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Exact check of the first 1,024 odd lower-endpoint positions, with
lookahead for a possible pair at the boundary. -/
theorem finiteTwinFirst1024_checked :
    (twinBitsetLowers (canonicalPrimeBaseList 46) 45 1024).card = 58 := by
  decide +kernel

theorem finiteTwinFirst1024_mathematical : (twinPrimeSegment 45 2093).card = 58 := by
  have h := twinBitsetLowers_spec (canonicalPrimeBaseList 46) 46 45 1024
    (canonicalPrimeBaseList_complete 46) (by decide) (by decide) (by decide)
  have hc := congrArg Finset.card h
  rw [finiteTwinFirst1024_checked] at hc
  simpa using hc.symm

/-- The checked prefix contributes genuine members of the full finite
source matching. This is a partial population result, not the FT count. -/
theorem finiteTwinSeeds_at_least_58 : 58 ≤ finiteTwinSeeds.card := by
  have hsub : twinPrimeSegment 45 2093 ⊆ finiteTwinSeeds := by
    intro p hp
    simp only [twinPrimeSegment, Finset.mem_filter, Finset.mem_Ico] at hp
    apply (mem_finiteTwinSeeds p).mpr
    exact ⟨by omega, hp.2.1, hp.2.2.1, by omega⟩
  have h := Finset.card_le_card hsub
  simpa [finiteTwinFirst1024_mathematical] using h

end
end Sude
