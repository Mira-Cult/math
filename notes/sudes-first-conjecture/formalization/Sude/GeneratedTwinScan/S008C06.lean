import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S008C05

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S008C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 17563693 widths0 = 159 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 17563693 17596461).card = 159 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 17563693 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 17563693 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 17563693 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 17596461 widths1 = 139 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 17596461 17629229).card = 139 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 17596461 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 17596461 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 17596461 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 17629229 widths2 = 147 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 17629229 17661997).card = 147 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 17629229 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 17629229 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 17629229 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 17661997 widths3 = 157 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 17661997 17694765).card = 157 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 17661997 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 17661997 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 17661997 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 17563693 17629229).card = 298 := by
  simpa using combineTwinPrimeSegments (by decide : 17563693 ≤ 17596461)
    (by decide : 17596461 ≤ 17629229) block0 block1

theorem join_0_1 : (twinPrimeSegment 17629229 17694765).card = 304 := by
  simpa using combineTwinPrimeSegments (by decide : 17629229 ≤ 17661997)
    (by decide : 17661997 ≤ 17694765) block2 block3

theorem join_1_0 : (twinPrimeSegment 17563693 17694765).card = 602 := by
  simpa using combineTwinPrimeSegments (by decide : 17563693 ≤ 17629229)
    (by decide : 17629229 ≤ 17694765) join_0_0 join_0_1

theorem total : (twinPrimeSegment 17563693 17694765).card = 602 := join_1_0

end S008C06
end Sude.GeneratedTwinScan
