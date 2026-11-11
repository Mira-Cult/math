import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S004C03

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S004C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 8912941 widths0 = 187 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 8912941 8945709).card = 187 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 8912941 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 8912941 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 8912941 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 8945709 widths1 = 162 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 8945709 8978477).card = 162 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 8945709 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 8945709 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 8945709 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 8978477 widths2 = 155 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 8978477 9011245).card = 155 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 8978477 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 8978477 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 8978477 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 9011245 widths3 = 168 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 9011245 9044013).card = 168 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 9011245 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 9011245 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 9011245 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 8912941 8978477).card = 349 := by
  simpa using combineTwinPrimeSegments (by decide : 8912941 ≤ 8945709)
    (by decide : 8945709 ≤ 8978477) block0 block1

theorem join_0_1 : (twinPrimeSegment 8978477 9044013).card = 323 := by
  simpa using combineTwinPrimeSegments (by decide : 8978477 ≤ 9011245)
    (by decide : 9011245 ≤ 9044013) block2 block3

theorem join_1_0 : (twinPrimeSegment 8912941 9044013).card = 672 := by
  simpa using combineTwinPrimeSegments (by decide : 8912941 ≤ 8978477)
    (by decide : 8978477 ≤ 9044013) join_0_0 join_0_1

theorem total : (twinPrimeSegment 8912941 9044013).card = 672 := join_1_0

end S004C04
end Sude.GeneratedTwinScan
