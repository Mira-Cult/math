import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S005C12

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S005C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 12189741 widths0 = 162 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 12189741 12222509).card = 162 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 12189741 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 12189741 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 12189741 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 12222509 widths1 = 182 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 12222509 12255277).card = 182 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 12222509 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 12222509 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 12222509 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 12255277 widths2 = 167 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 12255277 12288045).card = 167 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 12255277 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 12255277 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 12255277 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 12288045 widths3 = 152 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 12288045 12320813).card = 152 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 12288045 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 12288045 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 12288045 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 12189741 12255277).card = 344 := by
  simpa using combineTwinPrimeSegments (by decide : 12189741 ≤ 12222509)
    (by decide : 12222509 ≤ 12255277) block0 block1

theorem join_0_1 : (twinPrimeSegment 12255277 12320813).card = 319 := by
  simpa using combineTwinPrimeSegments (by decide : 12255277 ≤ 12288045)
    (by decide : 12288045 ≤ 12320813) block2 block3

theorem join_1_0 : (twinPrimeSegment 12189741 12320813).card = 663 := by
  simpa using combineTwinPrimeSegments (by decide : 12189741 ≤ 12255277)
    (by decide : 12255277 ≤ 12320813) join_0_0 join_0_1

theorem total : (twinPrimeSegment 12189741 12320813).card = 663 := join_1_0

end S005C13
end Sude.GeneratedTwinScan
