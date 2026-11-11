import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S002C09

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S002C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 5505069 widths0 = 194 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 5505069 5537837).card = 194 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 5505069 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 5505069 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 5505069 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 5537837 widths1 = 178 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 5537837 5570605).card = 178 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 5537837 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 5537837 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 5537837 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 5570605 widths2 = 186 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 5570605 5603373).card = 186 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 5570605 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 5570605 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 5570605 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 5603373 widths3 = 174 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 5603373 5636141).card = 174 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 5603373 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 5603373 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 5603373 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 5505069 5570605).card = 372 := by
  simpa using combineTwinPrimeSegments (by decide : 5505069 ≤ 5537837)
    (by decide : 5537837 ≤ 5570605) block0 block1

theorem join_0_1 : (twinPrimeSegment 5570605 5636141).card = 360 := by
  simpa using combineTwinPrimeSegments (by decide : 5570605 ≤ 5603373)
    (by decide : 5603373 ≤ 5636141) block2 block3

theorem join_1_0 : (twinPrimeSegment 5505069 5636141).card = 732 := by
  simpa using combineTwinPrimeSegments (by decide : 5505069 ≤ 5570605)
    (by decide : 5570605 ≤ 5636141) join_0_0 join_0_1

theorem total : (twinPrimeSegment 5505069 5636141).card = 732 := join_1_0

end S002C10
end Sude.GeneratedTwinScan
