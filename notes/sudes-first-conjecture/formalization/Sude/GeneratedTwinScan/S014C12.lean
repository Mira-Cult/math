import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S014C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 30933037 widths0 = 140 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 30933037 30965805).card = 140 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 30933037 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 30933037 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 30933037 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 30965805 widths1 = 135 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 30965805 30998573).card = 135 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 30965805 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 30965805 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 30965805 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 30998573 widths2 = 140 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 30998573 31031341).card = 140 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 30998573 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 30998573 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 30998573 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 31031341 widths3 = 146 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 31031341 31064109).card = 146 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 31031341 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 31031341 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 31031341 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 30933037 30998573).card = 275 := by
  simpa using combineTwinPrimeSegments (by decide : 30933037 ≤ 30965805)
    (by decide : 30965805 ≤ 30998573) block0 block1

theorem join_0_1 : (twinPrimeSegment 30998573 31064109).card = 286 := by
  simpa using combineTwinPrimeSegments (by decide : 30998573 ≤ 31031341)
    (by decide : 31031341 ≤ 31064109) block2 block3

theorem join_1_0 : (twinPrimeSegment 30933037 31064109).card = 561 := by
  simpa using combineTwinPrimeSegments (by decide : 30933037 ≤ 30998573)
    (by decide : 30998573 ≤ 31064109) join_0_0 join_0_1

theorem total : (twinPrimeSegment 30933037 31064109).card = 561 := join_1_0

end S014C12
end Sude.GeneratedTwinScan
