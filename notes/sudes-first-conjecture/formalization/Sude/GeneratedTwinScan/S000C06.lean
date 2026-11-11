import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S000C05

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S000C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 786477 widths0 = 216 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 786477 819245).card = 216 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 786477 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 786477 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 786477 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 819245 widths1 = 237 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 819245 852013).card = 237 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 819245 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 819245 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 819245 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 852013 widths2 = 245 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 852013 884781).card = 245 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 852013 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 852013 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 852013 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 884781 widths3 = 231 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 884781 917549).card = 231 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 884781 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 884781 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 884781 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 786477 852013).card = 453 := by
  simpa using combineTwinPrimeSegments (by decide : 786477 ≤ 819245)
    (by decide : 819245 ≤ 852013) block0 block1

theorem join_0_1 : (twinPrimeSegment 852013 917549).card = 476 := by
  simpa using combineTwinPrimeSegments (by decide : 852013 ≤ 884781)
    (by decide : 884781 ≤ 917549) block2 block3

theorem join_1_0 : (twinPrimeSegment 786477 917549).card = 929 := by
  simpa using combineTwinPrimeSegments (by decide : 786477 ≤ 852013)
    (by decide : 852013 ≤ 917549) join_0_0 join_0_1

theorem total : (twinPrimeSegment 786477 917549).card = 929 := join_1_0

end S000C06
end Sude.GeneratedTwinScan
