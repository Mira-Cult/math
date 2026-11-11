import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S257C05

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S257C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 539754541 widths0 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 539754541 539787309).card = 116 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 539754541 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 539754541 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 539754541 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 539787309 widths1 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 539787309 539820077).card = 116 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 539787309 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 539787309 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 539787309 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 539820077 widths2 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 539820077 539852845).card = 105 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 539820077 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 539820077 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 539820077 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 539852845 widths3 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 539852845 539885613).card = 105 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 539852845 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 539852845 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 539852845 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 539754541 539820077).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 539754541 ≤ 539787309)
    (by decide : 539787309 ≤ 539820077) block0 block1

theorem join_0_1 : (twinPrimeSegment 539820077 539885613).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 539820077 ≤ 539852845)
    (by decide : 539852845 ≤ 539885613) block2 block3

theorem join_1_0 : (twinPrimeSegment 539754541 539885613).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 539754541 ≤ 539820077)
    (by decide : 539820077 ≤ 539885613) join_0_0 join_0_1

theorem total : (twinPrimeSegment 539754541 539885613).card = 442 := join_1_0

end S257C06
end Sude.GeneratedTwinScan
