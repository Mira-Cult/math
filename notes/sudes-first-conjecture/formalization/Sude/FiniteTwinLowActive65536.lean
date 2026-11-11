import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! Four kernel-checked FT blocks from the lower end. -/
namespace Sude
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def finiteTwinLowBlockWidths : List ℕ := List.replicate 4 4096

theorem finiteTwinLowBlock0_checked :
    activeStreamingTwinScan finiteTwinCheckedBase 45 finiteTwinLowBlockWidths = 500 := by
  decide +kernel

theorem finiteTwinLowBlock0_mathematical :
    (twinPrimeSegment 45 32813).card = 500 := by
  have hstream := (activeStreamingTwinScan_eq finiteTwinCheckedBase 45 finiteTwinLowBlockWidths).symm.trans
    finiteTwinLowBlock0_checked
  have hscan := (streamingTwinScan_eq finiteTwinCheckedBase 45 finiteTwinLowBlockWidths).symm.trans hstream
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 45 finiteTwinLowBlockWidths
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hscan] at h
  simpa [finiteTwinLowBlockWidths] using h.symm

theorem finiteTwinLowBlock1_checked :
    activeStreamingTwinScan finiteTwinCheckedBase 32813 finiteTwinLowBlockWidths = 356 := by
  decide +kernel

theorem finiteTwinLowBlock1_mathematical :
    (twinPrimeSegment 32813 65581).card = 356 := by
  have hstream := (activeStreamingTwinScan_eq finiteTwinCheckedBase 32813 finiteTwinLowBlockWidths).symm.trans
    finiteTwinLowBlock1_checked
  have hscan := (streamingTwinScan_eq finiteTwinCheckedBase 32813 finiteTwinLowBlockWidths).symm.trans hstream
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 32813 finiteTwinLowBlockWidths
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hscan] at h
  simpa [finiteTwinLowBlockWidths] using h.symm

theorem finiteTwinLowBlock2_checked :
    activeStreamingTwinScan finiteTwinCheckedBase 65581 finiteTwinLowBlockWidths = 344 := by
  decide +kernel

theorem finiteTwinLowBlock2_mathematical :
    (twinPrimeSegment 65581 98349).card = 344 := by
  have hstream := (activeStreamingTwinScan_eq finiteTwinCheckedBase 65581 finiteTwinLowBlockWidths).symm.trans
    finiteTwinLowBlock2_checked
  have hscan := (streamingTwinScan_eq finiteTwinCheckedBase 65581 finiteTwinLowBlockWidths).symm.trans hstream
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 65581 finiteTwinLowBlockWidths
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hscan] at h
  simpa [finiteTwinLowBlockWidths] using h.symm

theorem finiteTwinLowBlock3_checked :
    activeStreamingTwinScan finiteTwinCheckedBase 98349 finiteTwinLowBlockWidths = 321 := by
  decide +kernel

theorem finiteTwinLowBlock3_mathematical :
    (twinPrimeSegment 98349 131117).card = 321 := by
  have hstream := (activeStreamingTwinScan_eq finiteTwinCheckedBase 98349 finiteTwinLowBlockWidths).symm.trans
    finiteTwinLowBlock3_checked
  have hscan := (streamingTwinScan_eq finiteTwinCheckedBase 98349 finiteTwinLowBlockWidths).symm.trans hstream
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 98349 finiteTwinLowBlockWidths
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hscan] at h
  simpa [finiteTwinLowBlockWidths] using h.symm

/-- The four independently checked blocks exactly cover the first 65,536
odd lower-endpoint positions. -/
theorem finiteTwinLow65536_mathematical : (twinPrimeSegment 45 131117).card = 1521 := by
  have h01 : (twinPrimeSegment 45 65581).card = 856 := by
    simpa using combineTwinPrimeSegments (by decide : 45 ≤ 32813) (by decide : 32813 ≤ 65581)
      finiteTwinLowBlock0_mathematical finiteTwinLowBlock1_mathematical
  have h23 : (twinPrimeSegment 65581 131117).card = 665 := by
    simpa using combineTwinPrimeSegments (by decide : 65581 ≤ 98349) (by decide : 98349 ≤ 131117)
      finiteTwinLowBlock2_mathematical finiteTwinLowBlock3_mathematical
  simpa using combineTwinPrimeSegments (by decide : 45 ≤ 65581) (by decide : 65581 ≤ 131117) h01 h23

end
end Sude
