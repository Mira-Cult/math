import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S004C07

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S004C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 9437229 widths0 = 183 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 9437229 9469997).card = 183 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 9437229 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 9437229 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 9437229 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 9469997 widths1 = 155 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 9469997 9502765).card = 155 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 9469997 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 9469997 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 9469997 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 9502765 widths2 = 147 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 9502765 9535533).card = 147 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 9502765 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 9502765 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 9502765 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 9535533 widths3 = 198 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 9535533 9568301).card = 198 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 9535533 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 9535533 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 9535533 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 9437229 9502765).card = 338 := by
  simpa using combineTwinPrimeSegments (by decide : 9437229 ≤ 9469997)
    (by decide : 9469997 ≤ 9502765) block0 block1

theorem join_0_1 : (twinPrimeSegment 9502765 9568301).card = 345 := by
  simpa using combineTwinPrimeSegments (by decide : 9502765 ≤ 9535533)
    (by decide : 9535533 ≤ 9568301) block2 block3

theorem join_1_0 : (twinPrimeSegment 9437229 9568301).card = 683 := by
  simpa using combineTwinPrimeSegments (by decide : 9437229 ≤ 9502765)
    (by decide : 9502765 ≤ 9568301) join_0_0 join_0_1

theorem total : (twinPrimeSegment 9437229 9568301).card = 683 := join_1_0

end S004C08
end Sude.GeneratedTwinScan
