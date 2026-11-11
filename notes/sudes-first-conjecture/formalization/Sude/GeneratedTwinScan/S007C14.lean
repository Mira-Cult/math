import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S007C13

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S007C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 16515117 widths0 = 147 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 16515117 16547885).card = 147 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 16515117 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 16515117 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 16515117 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 16547885 widths1 = 173 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 16547885 16580653).card = 173 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 16547885 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 16547885 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 16547885 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 16580653 widths2 = 180 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 16580653 16613421).card = 180 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 16580653 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 16580653 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 16580653 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 16613421 widths3 = 167 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 16613421 16646189).card = 167 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 16613421 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 16613421 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 16613421 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 16515117 16580653).card = 320 := by
  simpa using combineTwinPrimeSegments (by decide : 16515117 ≤ 16547885)
    (by decide : 16547885 ≤ 16580653) block0 block1

theorem join_0_1 : (twinPrimeSegment 16580653 16646189).card = 347 := by
  simpa using combineTwinPrimeSegments (by decide : 16580653 ≤ 16613421)
    (by decide : 16613421 ≤ 16646189) block2 block3

theorem join_1_0 : (twinPrimeSegment 16515117 16646189).card = 667 := by
  simpa using combineTwinPrimeSegments (by decide : 16515117 ≤ 16580653)
    (by decide : 16580653 ≤ 16646189) join_0_0 join_0_1

theorem total : (twinPrimeSegment 16515117 16646189).card = 667 := join_1_0

end S007C14
end Sude.GeneratedTwinScan
