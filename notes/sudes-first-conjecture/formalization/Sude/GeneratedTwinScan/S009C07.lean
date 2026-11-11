import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S009C06

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S009C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 19791917 widths0 = 151 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 19791917 19824685).card = 151 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 19791917 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 19791917 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 19791917 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 19824685 widths1 = 137 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 19824685 19857453).card = 137 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 19824685 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 19824685 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 19824685 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 19857453 widths2 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 19857453 19890221).card = 137 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 19857453 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 19857453 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 19857453 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 19890221 widths3 = 158 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 19890221 19922989).card = 158 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 19890221 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 19890221 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 19890221 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 19791917 19857453).card = 288 := by
  simpa using combineTwinPrimeSegments (by decide : 19791917 ≤ 19824685)
    (by decide : 19824685 ≤ 19857453) block0 block1

theorem join_0_1 : (twinPrimeSegment 19857453 19922989).card = 295 := by
  simpa using combineTwinPrimeSegments (by decide : 19857453 ≤ 19890221)
    (by decide : 19890221 ≤ 19922989) block2 block3

theorem join_1_0 : (twinPrimeSegment 19791917 19922989).card = 583 := by
  simpa using combineTwinPrimeSegments (by decide : 19791917 ≤ 19857453)
    (by decide : 19857453 ≤ 19922989) join_0_0 join_0_1

theorem total : (twinPrimeSegment 19791917 19922989).card = 583 := join_1_0

end S009C07
end Sude.GeneratedTwinScan
