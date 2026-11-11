import Sude.FiniteTwinSeed
import Sude.TwinStreaming

/-! Four kernel-checked streamed FT segments. -/
namespace Sude
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def finiteTwinFirst4096Widths : List ℕ := List.replicate 4 1024

theorem finiteTwinFirst4096_checked :
    streamingTwinScan (canonicalPrimeBaseList 91) 45 finiteTwinFirst4096Widths = 173 := by
  decide +kernel

theorem finiteTwinFirst4096_mathematical : (twinPrimeSegment 45 8237).card = 173 := by
  have hscan := (streamingTwinScan_eq (canonicalPrimeBaseList 91) 45 finiteTwinFirst4096Widths).symm.trans
    finiteTwinFirst4096_checked
  have h := twinBitsetCountScan_spec (canonicalPrimeBaseList 91) 91 45 finiteTwinFirst4096Widths
    (canonicalPrimeBaseList_complete 91) (by decide) (by decide) (by decide)
  rw [hscan] at h
  simpa [finiteTwinFirst4096Widths] using h.symm

/-- These 173 checked pairs belong to the full source seed set. -/
theorem finiteTwinSeeds_at_least_173 : 173 ≤ finiteTwinSeeds.card := by
  have hsub : twinPrimeSegment 45 8237 ⊆ finiteTwinSeeds := by
    intro p hp
    simp only [twinPrimeSegment, Finset.mem_filter, Finset.mem_Ico] at hp
    apply (mem_finiteTwinSeeds p).mpr
    exact ⟨by omega, hp.2.1, hp.2.2.1, by omega⟩
  have h := Finset.card_le_card hsub
  simpa [finiteTwinFirst4096_mathematical] using h

/-- Acceptance of the full streaming plan implies the FT population. The
acceptance hypothesis is an unresolved internal numerical obligation. -/
theorem finiteTwinSeeds_count_of_streaming_scan
    (hscan : streamingTwinScan (canonicalPrimeBaseList 32768) 45 finiteTwinSeedWidths = 3650551) :
    finiteTwinSeeds.card = 3650551 := by
  apply finiteTwinSeeds_count_of_scan
  rw [← streamingTwinScan_eq]
  exact hscan

end
end Sude
