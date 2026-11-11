import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S257C06

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S257C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 539885613 widths0 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 539885613 539918381).card = 100 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 539885613 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 539885613 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 539885613 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 539918381 widths1 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 539918381 539951149).card = 100 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 539918381 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 539918381 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 539918381 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 539951149 widths2 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 539951149 539983917).card = 104 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 539951149 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 539951149 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 539951149 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 539983917 widths3 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 539983917 540016685).card = 105 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 539983917 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 539983917 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 539983917 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 539885613 539951149).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 539885613 ≤ 539918381)
    (by decide : 539918381 ≤ 539951149) block0 block1

theorem join_0_1 : (twinPrimeSegment 539951149 540016685).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 539951149 ≤ 539983917)
    (by decide : 539983917 ≤ 540016685) block2 block3

theorem join_1_0 : (twinPrimeSegment 539885613 540016685).card = 409 := by
  simpa using combineTwinPrimeSegments (by decide : 539885613 ≤ 539951149)
    (by decide : 539951149 ≤ 540016685) join_0_0 join_0_1

theorem total : (twinPrimeSegment 539885613 540016685).card = 409 := join_1_0

end S257C07
end Sude.GeneratedTwinScan
