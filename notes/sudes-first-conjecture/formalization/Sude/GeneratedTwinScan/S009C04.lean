import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S009C03

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S009C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 19398701 widths0 = 153 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 19398701 19431469).card = 153 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 19398701 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 19398701 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 19398701 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 19431469 widths1 = 152 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 19431469 19464237).card = 152 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 19431469 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 19431469 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 19431469 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 19464237 widths2 = 143 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 19464237 19497005).card = 143 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 19464237 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 19464237 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 19464237 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 19497005 widths3 = 145 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 19497005 19529773).card = 145 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 19497005 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 19497005 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 19497005 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 19398701 19464237).card = 305 := by
  simpa using combineTwinPrimeSegments (by decide : 19398701 ≤ 19431469)
    (by decide : 19431469 ≤ 19464237) block0 block1

theorem join_0_1 : (twinPrimeSegment 19464237 19529773).card = 288 := by
  simpa using combineTwinPrimeSegments (by decide : 19464237 ≤ 19497005)
    (by decide : 19497005 ≤ 19529773) block2 block3

theorem join_1_0 : (twinPrimeSegment 19398701 19529773).card = 593 := by
  simpa using combineTwinPrimeSegments (by decide : 19398701 ≤ 19464237)
    (by decide : 19464237 ≤ 19529773) join_0_0 join_0_1

theorem total : (twinPrimeSegment 19398701 19529773).card = 593 := join_1_0

end S009C04
end Sude.GeneratedTwinScan
