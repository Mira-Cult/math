import Sude.FiniteTwinSeed
import Sude.TwinStreaming

/-! Sixteen kernel-checked FT segments. -/
namespace Sude
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def finiteTwinFirst16384Widths : List ℕ := List.replicate 16 1024

theorem finiteTwinFirst16384_checked :
    streamingTwinScan (canonicalPrimeBaseList 181) 45 finiteTwinFirst16384Widths = 500 := by
  decide +kernel

theorem finiteTwinFirst16384_mathematical : (twinPrimeSegment 45 32813).card = 500 := by
  have hscan := (streamingTwinScan_eq (canonicalPrimeBaseList 181) 45 finiteTwinFirst16384Widths).symm.trans
    finiteTwinFirst16384_checked
  have h := twinBitsetCountScan_spec (canonicalPrimeBaseList 181) 181 45 finiteTwinFirst16384Widths
    (canonicalPrimeBaseList_complete 181) (by decide) (by decide) (by decide)
  rw [hscan] at h
  simpa [finiteTwinFirst16384Widths] using h.symm

theorem finiteTwinSeeds_at_least_500 : 500 ≤ finiteTwinSeeds.card := by
  have hsub : twinPrimeSegment 45 32813 ⊆ finiteTwinSeeds := by
    intro p hp
    simp only [twinPrimeSegment, Finset.mem_filter, Finset.mem_Ico] at hp
    apply (mem_finiteTwinSeeds p).mpr
    exact ⟨by omega, hp.2.1, hp.2.2.1, by omega⟩
  have h := Finset.card_le_card hsub
  simpa [finiteTwinFirst16384_mathematical] using h

end
end Sude
