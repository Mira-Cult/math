import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S013C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 27787309 widths0 = 168 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 27787309 27820077).card = 168 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 27787309 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 27787309 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 27787309 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 27820077 widths1 = 143 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 27820077 27852845).card = 143 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 27820077 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 27820077 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 27820077 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 27852845 widths2 = 152 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 27852845 27885613).card = 152 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 27852845 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 27852845 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 27852845 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 27885613 widths3 = 160 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 27885613 27918381).card = 160 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 27885613 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 27885613 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 27885613 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 27787309 27852845).card = 311 := by
  simpa using combineTwinPrimeSegments (by decide : 27787309 ≤ 27820077)
    (by decide : 27820077 ≤ 27852845) block0 block1

theorem join_0_1 : (twinPrimeSegment 27852845 27918381).card = 312 := by
  simpa using combineTwinPrimeSegments (by decide : 27852845 ≤ 27885613)
    (by decide : 27885613 ≤ 27918381) block2 block3

theorem join_1_0 : (twinPrimeSegment 27787309 27918381).card = 623 := by
  simpa using combineTwinPrimeSegments (by decide : 27787309 ≤ 27852845)
    (by decide : 27852845 ≤ 27918381) join_0_0 join_0_1

theorem total : (twinPrimeSegment 27787309 27918381).card = 623 := join_1_0

end S013C04
end Sude.GeneratedTwinScan
