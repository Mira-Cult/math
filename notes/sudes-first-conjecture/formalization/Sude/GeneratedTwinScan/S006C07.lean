import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S006C06

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S006C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 13500461 widths0 = 143 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 13500461 13533229).card = 143 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 13500461 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 13500461 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 13500461 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 13533229 widths1 = 163 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 13533229 13565997).card = 163 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 13533229 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 13533229 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 13533229 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 13565997 widths2 = 168 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 13565997 13598765).card = 168 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 13565997 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 13565997 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 13565997 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 13598765 widths3 = 150 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 13598765 13631533).card = 150 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 13598765 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 13598765 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 13598765 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 13500461 13565997).card = 306 := by
  simpa using combineTwinPrimeSegments (by decide : 13500461 ≤ 13533229)
    (by decide : 13533229 ≤ 13565997) block0 block1

theorem join_0_1 : (twinPrimeSegment 13565997 13631533).card = 318 := by
  simpa using combineTwinPrimeSegments (by decide : 13565997 ≤ 13598765)
    (by decide : 13598765 ≤ 13631533) block2 block3

theorem join_1_0 : (twinPrimeSegment 13500461 13631533).card = 624 := by
  simpa using combineTwinPrimeSegments (by decide : 13500461 ≤ 13565997)
    (by decide : 13565997 ≤ 13631533) join_0_0 join_0_1

theorem total : (twinPrimeSegment 13500461 13631533).card = 624 := join_1_0

end S006C07
end Sude.GeneratedTwinScan
