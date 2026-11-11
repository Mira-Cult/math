import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S005C13

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S005C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 12320813 widths0 = 150 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 12320813 12353581).card = 150 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 12320813 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 12320813 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 12320813 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 12353581 widths1 = 166 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 12353581 12386349).card = 166 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 12353581 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 12353581 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 12353581 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 12386349 widths2 = 171 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 12386349 12419117).card = 171 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 12386349 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 12386349 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 12386349 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 12419117 widths3 = 164 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 12419117 12451885).card = 164 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 12419117 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 12419117 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 12419117 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 12320813 12386349).card = 316 := by
  simpa using combineTwinPrimeSegments (by decide : 12320813 ≤ 12353581)
    (by decide : 12353581 ≤ 12386349) block0 block1

theorem join_0_1 : (twinPrimeSegment 12386349 12451885).card = 335 := by
  simpa using combineTwinPrimeSegments (by decide : 12386349 ≤ 12419117)
    (by decide : 12419117 ≤ 12451885) block2 block3

theorem join_1_0 : (twinPrimeSegment 12320813 12451885).card = 651 := by
  simpa using combineTwinPrimeSegments (by decide : 12320813 ≤ 12386349)
    (by decide : 12386349 ≤ 12451885) join_0_0 join_0_1

theorem total : (twinPrimeSegment 12320813 12451885).card = 651 := join_1_0

end S005C14
end Sude.GeneratedTwinScan
