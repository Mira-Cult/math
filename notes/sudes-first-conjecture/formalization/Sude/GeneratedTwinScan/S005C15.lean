import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S005C14

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S005C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 12451885 widths0 = 172 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 12451885 12484653).card = 172 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 12451885 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 12451885 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 12451885 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 12484653 widths1 = 150 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 12484653 12517421).card = 150 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 12484653 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 12484653 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 12484653 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 12517421 widths2 = 141 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 12517421 12550189).card = 141 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 12517421 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 12517421 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 12517421 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 12550189 widths3 = 152 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 12550189 12582957).card = 152 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 12550189 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 12550189 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 12550189 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 12451885 12517421).card = 322 := by
  simpa using combineTwinPrimeSegments (by decide : 12451885 ≤ 12484653)
    (by decide : 12484653 ≤ 12517421) block0 block1

theorem join_0_1 : (twinPrimeSegment 12517421 12582957).card = 293 := by
  simpa using combineTwinPrimeSegments (by decide : 12517421 ≤ 12550189)
    (by decide : 12550189 ≤ 12582957) block2 block3

theorem join_1_0 : (twinPrimeSegment 12451885 12582957).card = 615 := by
  simpa using combineTwinPrimeSegments (by decide : 12451885 ≤ 12517421)
    (by decide : 12517421 ≤ 12582957) join_0_0 join_0_1

theorem total : (twinPrimeSegment 12451885 12582957).card = 615 := join_1_0

end S005C15
end Sude.GeneratedTwinScan
