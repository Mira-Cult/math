import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S001C00

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S001C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 2228269 widths0 = 223 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 2228269 2261037).card = 223 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 2228269 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 2228269 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 2228269 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 2261037 widths1 = 204 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 2261037 2293805).card = 204 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 2261037 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 2261037 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 2261037 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 2293805 widths2 = 187 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 2293805 2326573).card = 187 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 2293805 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 2293805 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 2293805 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 2326573 widths3 = 213 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 2326573 2359341).card = 213 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 2326573 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 2326573 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 2326573 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 2228269 2293805).card = 427 := by
  simpa using combineTwinPrimeSegments (by decide : 2228269 ≤ 2261037)
    (by decide : 2261037 ≤ 2293805) block0 block1

theorem join_0_1 : (twinPrimeSegment 2293805 2359341).card = 400 := by
  simpa using combineTwinPrimeSegments (by decide : 2293805 ≤ 2326573)
    (by decide : 2326573 ≤ 2359341) block2 block3

theorem join_1_0 : (twinPrimeSegment 2228269 2359341).card = 827 := by
  simpa using combineTwinPrimeSegments (by decide : 2228269 ≤ 2293805)
    (by decide : 2293805 ≤ 2359341) join_0_0 join_0_1

theorem total : (twinPrimeSegment 2228269 2359341).card = 827 := join_1_0

end S001C01
end Sude.GeneratedTwinScan
