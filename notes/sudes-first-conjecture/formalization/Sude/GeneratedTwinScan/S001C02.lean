import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S001C01

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S001C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 2359341 widths0 = 202 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 2359341 2392109).card = 202 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 2359341 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 2359341 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 2359341 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 2392109 widths1 = 191 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 2392109 2424877).card = 191 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 2392109 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 2392109 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 2392109 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 2424877 widths2 = 183 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 2424877 2457645).card = 183 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 2424877 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 2424877 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 2424877 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 2457645 widths3 = 200 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 2457645 2490413).card = 200 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 2457645 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 2457645 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 2457645 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 2359341 2424877).card = 393 := by
  simpa using combineTwinPrimeSegments (by decide : 2359341 ≤ 2392109)
    (by decide : 2392109 ≤ 2424877) block0 block1

theorem join_0_1 : (twinPrimeSegment 2424877 2490413).card = 383 := by
  simpa using combineTwinPrimeSegments (by decide : 2424877 ≤ 2457645)
    (by decide : 2457645 ≤ 2490413) block2 block3

theorem join_1_0 : (twinPrimeSegment 2359341 2490413).card = 776 := by
  simpa using combineTwinPrimeSegments (by decide : 2359341 ≤ 2424877)
    (by decide : 2424877 ≤ 2490413) join_0_0 join_0_1

theorem total : (twinPrimeSegment 2359341 2490413).card = 776 := join_1_0

end S001C02
end Sude.GeneratedTwinScan
