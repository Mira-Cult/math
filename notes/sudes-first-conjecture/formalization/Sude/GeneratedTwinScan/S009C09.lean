import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S009C08

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S009C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 20054061 widths0 = 153 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 20054061 20086829).card = 153 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 20054061 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 20054061 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 20054061 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 20086829 widths1 = 156 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 20086829 20119597).card = 156 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 20086829 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 20086829 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 20086829 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 20119597 widths2 = 150 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 20119597 20152365).card = 150 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 20119597 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 20119597 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 20119597 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 20152365 widths3 = 167 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 20152365 20185133).card = 167 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 20152365 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 20152365 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 20152365 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 20054061 20119597).card = 309 := by
  simpa using combineTwinPrimeSegments (by decide : 20054061 ≤ 20086829)
    (by decide : 20086829 ≤ 20119597) block0 block1

theorem join_0_1 : (twinPrimeSegment 20119597 20185133).card = 317 := by
  simpa using combineTwinPrimeSegments (by decide : 20119597 ≤ 20152365)
    (by decide : 20152365 ≤ 20185133) block2 block3

theorem join_1_0 : (twinPrimeSegment 20054061 20185133).card = 626 := by
  simpa using combineTwinPrimeSegments (by decide : 20054061 ≤ 20119597)
    (by decide : 20119597 ≤ 20185133) join_0_0 join_0_1

theorem total : (twinPrimeSegment 20054061 20185133).card = 626 := join_1_0

end S009C09
end Sude.GeneratedTwinScan
