import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S013C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 27394093 widths0 = 145 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 27394093 27426861).card = 145 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 27394093 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 27394093 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 27394093 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 27426861 widths1 = 143 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 27426861 27459629).card = 143 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 27426861 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 27426861 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 27426861 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 27459629 widths2 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 27459629 27492397).card = 126 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 27459629 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 27459629 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 27459629 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 27492397 widths3 = 150 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 27492397 27525165).card = 150 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 27492397 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 27492397 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 27492397 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 27394093 27459629).card = 288 := by
  simpa using combineTwinPrimeSegments (by decide : 27394093 ≤ 27426861)
    (by decide : 27426861 ≤ 27459629) block0 block1

theorem join_0_1 : (twinPrimeSegment 27459629 27525165).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 27459629 ≤ 27492397)
    (by decide : 27492397 ≤ 27525165) block2 block3

theorem join_1_0 : (twinPrimeSegment 27394093 27525165).card = 564 := by
  simpa using combineTwinPrimeSegments (by decide : 27394093 ≤ 27459629)
    (by decide : 27459629 ≤ 27525165) join_0_0 join_0_1

theorem total : (twinPrimeSegment 27394093 27525165).card = 564 := join_1_0

end S013C01
end Sude.GeneratedTwinScan
