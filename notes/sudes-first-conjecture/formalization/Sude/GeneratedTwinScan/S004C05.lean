import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S004C04

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S004C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 9044013 widths0 = 157 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 9044013 9076781).card = 157 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 9044013 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 9044013 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 9044013 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 9076781 widths1 = 185 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 9076781 9109549).card = 185 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 9076781 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 9076781 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 9076781 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 9109549 widths2 = 168 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 9109549 9142317).card = 168 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 9109549 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 9109549 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 9109549 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 9142317 widths3 = 165 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 9142317 9175085).card = 165 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 9142317 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 9142317 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 9142317 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 9044013 9109549).card = 342 := by
  simpa using combineTwinPrimeSegments (by decide : 9044013 ≤ 9076781)
    (by decide : 9076781 ≤ 9109549) block0 block1

theorem join_0_1 : (twinPrimeSegment 9109549 9175085).card = 333 := by
  simpa using combineTwinPrimeSegments (by decide : 9109549 ≤ 9142317)
    (by decide : 9142317 ≤ 9175085) block2 block3

theorem join_1_0 : (twinPrimeSegment 9044013 9175085).card = 675 := by
  simpa using combineTwinPrimeSegments (by decide : 9044013 ≤ 9109549)
    (by decide : 9109549 ≤ 9175085) join_0_0 join_0_1

theorem total : (twinPrimeSegment 9044013 9175085).card = 675 := join_1_0

end S004C05
end Sude.GeneratedTwinScan
