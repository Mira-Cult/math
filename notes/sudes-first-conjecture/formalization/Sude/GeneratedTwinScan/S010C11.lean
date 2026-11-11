import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S010C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 22413357 widths0 = 145 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 22413357 22446125).card = 145 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 22413357 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 22413357 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 22413357 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 22446125 widths1 = 164 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 22446125 22478893).card = 164 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 22446125 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 22446125 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 22446125 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 22478893 widths2 = 148 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 22478893 22511661).card = 148 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 22478893 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 22478893 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 22478893 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 22511661 widths3 = 148 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 22511661 22544429).card = 148 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 22511661 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 22511661 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 22511661 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 22413357 22478893).card = 309 := by
  simpa using combineTwinPrimeSegments (by decide : 22413357 ≤ 22446125)
    (by decide : 22446125 ≤ 22478893) block0 block1

theorem join_0_1 : (twinPrimeSegment 22478893 22544429).card = 296 := by
  simpa using combineTwinPrimeSegments (by decide : 22478893 ≤ 22511661)
    (by decide : 22511661 ≤ 22544429) block2 block3

theorem join_1_0 : (twinPrimeSegment 22413357 22544429).card = 605 := by
  simpa using combineTwinPrimeSegments (by decide : 22413357 ≤ 22478893)
    (by decide : 22478893 ≤ 22544429) join_0_0 join_0_1

theorem total : (twinPrimeSegment 22413357 22544429).card = 605 := join_1_0

end S010C11
end Sude.GeneratedTwinScan
