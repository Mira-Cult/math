import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S258C13

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S258C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 542900269 widths0 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 542900269 542933037).card = 106 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 542900269 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 542900269 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 542900269 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 542933037 widths1 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 542933037 542965805).card = 120 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 542933037 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 542933037 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 542933037 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 542965805 widths2 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 542965805 542998573).card = 106 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 542965805 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 542965805 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 542965805 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 542998573 widths3 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 542998573 543031341).card = 115 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 542998573 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 542998573 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 542998573 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 542900269 542965805).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 542900269 ≤ 542933037)
    (by decide : 542933037 ≤ 542965805) block0 block1

theorem join_0_1 : (twinPrimeSegment 542965805 543031341).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 542965805 ≤ 542998573)
    (by decide : 542998573 ≤ 543031341) block2 block3

theorem join_1_0 : (twinPrimeSegment 542900269 543031341).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 542900269 ≤ 542965805)
    (by decide : 542965805 ≤ 543031341) join_0_0 join_0_1

theorem total : (twinPrimeSegment 542900269 543031341).card = 447 := join_1_0

end S258C14
end Sude.GeneratedTwinScan
