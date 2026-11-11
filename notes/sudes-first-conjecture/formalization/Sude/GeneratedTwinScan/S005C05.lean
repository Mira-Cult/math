import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S005C04

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S005C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 11141165 widths0 = 178 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 11141165 11173933).card = 178 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 11141165 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 11141165 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 11141165 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 11173933 widths1 = 167 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 11173933 11206701).card = 167 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 11173933 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 11173933 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 11173933 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 11206701 widths2 = 166 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 11206701 11239469).card = 166 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 11206701 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 11206701 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 11206701 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 11239469 widths3 = 162 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 11239469 11272237).card = 162 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 11239469 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 11239469 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 11239469 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 11141165 11206701).card = 345 := by
  simpa using combineTwinPrimeSegments (by decide : 11141165 ≤ 11173933)
    (by decide : 11173933 ≤ 11206701) block0 block1

theorem join_0_1 : (twinPrimeSegment 11206701 11272237).card = 328 := by
  simpa using combineTwinPrimeSegments (by decide : 11206701 ≤ 11239469)
    (by decide : 11239469 ≤ 11272237) block2 block3

theorem join_1_0 : (twinPrimeSegment 11141165 11272237).card = 673 := by
  simpa using combineTwinPrimeSegments (by decide : 11141165 ≤ 11206701)
    (by decide : 11206701 ≤ 11272237) join_0_0 join_0_1

theorem total : (twinPrimeSegment 11141165 11272237).card = 673 := join_1_0

end S005C05
end Sude.GeneratedTwinScan
