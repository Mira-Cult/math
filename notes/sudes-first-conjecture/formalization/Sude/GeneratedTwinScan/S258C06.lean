import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S258C05

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S258C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 541851693 widths0 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 541851693 541884461).card = 120 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 541851693 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 541851693 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 541851693 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 541884461 widths1 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 541884461 541917229).card = 105 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 541884461 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 541884461 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 541884461 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 541917229 widths2 = 96 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 541917229 541949997).card = 96 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 541917229 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 541917229 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 541917229 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 541949997 widths3 = 93 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 541949997 541982765).card = 93 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 541949997 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 541949997 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 541949997 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 541851693 541917229).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 541851693 ≤ 541884461)
    (by decide : 541884461 ≤ 541917229) block0 block1

theorem join_0_1 : (twinPrimeSegment 541917229 541982765).card = 189 := by
  simpa using combineTwinPrimeSegments (by decide : 541917229 ≤ 541949997)
    (by decide : 541949997 ≤ 541982765) block2 block3

theorem join_1_0 : (twinPrimeSegment 541851693 541982765).card = 414 := by
  simpa using combineTwinPrimeSegments (by decide : 541851693 ≤ 541917229)
    (by decide : 541917229 ≤ 541982765) join_0_0 join_0_1

theorem total : (twinPrimeSegment 541851693 541982765).card = 414 := join_1_0

end S258C06
end Sude.GeneratedTwinScan
