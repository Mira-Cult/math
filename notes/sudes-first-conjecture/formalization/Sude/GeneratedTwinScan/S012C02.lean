import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S012C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 25428013 widths0 = 158 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 25428013 25460781).card = 158 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 25428013 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 25428013 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 25428013 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 25460781 widths1 = 158 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 25460781 25493549).card = 158 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 25460781 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 25460781 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 25460781 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 25493549 widths2 = 161 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 25493549 25526317).card = 161 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 25493549 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 25493549 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 25493549 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 25526317 widths3 = 149 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 25526317 25559085).card = 149 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 25526317 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 25526317 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 25526317 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 25428013 25493549).card = 316 := by
  simpa using combineTwinPrimeSegments (by decide : 25428013 ≤ 25460781)
    (by decide : 25460781 ≤ 25493549) block0 block1

theorem join_0_1 : (twinPrimeSegment 25493549 25559085).card = 310 := by
  simpa using combineTwinPrimeSegments (by decide : 25493549 ≤ 25526317)
    (by decide : 25526317 ≤ 25559085) block2 block3

theorem join_1_0 : (twinPrimeSegment 25428013 25559085).card = 626 := by
  simpa using combineTwinPrimeSegments (by decide : 25428013 ≤ 25493549)
    (by decide : 25493549 ≤ 25559085) join_0_0 join_0_1

theorem total : (twinPrimeSegment 25428013 25559085).card = 626 := join_1_0

end S012C02
end Sude.GeneratedTwinScan
