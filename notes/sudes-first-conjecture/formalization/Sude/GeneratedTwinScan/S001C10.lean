import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S001C09

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S001C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 3407917 widths0 = 197 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 3407917 3440685).card = 197 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 3407917 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 3407917 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 3407917 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 3440685 widths1 = 185 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 3440685 3473453).card = 185 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 3440685 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 3440685 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 3440685 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 3473453 widths2 = 179 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 3473453 3506221).card = 179 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 3473453 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 3473453 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 3473453 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 3506221 widths3 = 193 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 3506221 3538989).card = 193 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 3506221 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 3506221 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 3506221 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 3407917 3473453).card = 382 := by
  simpa using combineTwinPrimeSegments (by decide : 3407917 ≤ 3440685)
    (by decide : 3440685 ≤ 3473453) block0 block1

theorem join_0_1 : (twinPrimeSegment 3473453 3538989).card = 372 := by
  simpa using combineTwinPrimeSegments (by decide : 3473453 ≤ 3506221)
    (by decide : 3506221 ≤ 3538989) block2 block3

theorem join_1_0 : (twinPrimeSegment 3407917 3538989).card = 754 := by
  simpa using combineTwinPrimeSegments (by decide : 3407917 ≤ 3473453)
    (by decide : 3473453 ≤ 3538989) join_0_0 join_0_1

theorem total : (twinPrimeSegment 3407917 3538989).card = 754 := join_1_0

end S001C10
end Sude.GeneratedTwinScan
