import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S257C11

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S257C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 540540973 widths0 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 540540973 540573741).card = 117 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 540540973 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 540540973 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 540540973 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 540573741 widths1 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 540573741 540606509).card = 100 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 540573741 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 540573741 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 540573741 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 540606509 widths2 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 540606509 540639277).card = 111 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 540606509 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 540606509 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 540606509 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 540639277 widths3 = 90 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 540639277 540672045).card = 90 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 540639277 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 540639277 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 540639277 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 540540973 540606509).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 540540973 ≤ 540573741)
    (by decide : 540573741 ≤ 540606509) block0 block1

theorem join_0_1 : (twinPrimeSegment 540606509 540672045).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 540606509 ≤ 540639277)
    (by decide : 540639277 ≤ 540672045) block2 block3

theorem join_1_0 : (twinPrimeSegment 540540973 540672045).card = 418 := by
  simpa using combineTwinPrimeSegments (by decide : 540540973 ≤ 540606509)
    (by decide : 540606509 ≤ 540672045) join_0_0 join_0_1

theorem total : (twinPrimeSegment 540540973 540672045).card = 418 := join_1_0

end S257C12
end Sude.GeneratedTwinScan
