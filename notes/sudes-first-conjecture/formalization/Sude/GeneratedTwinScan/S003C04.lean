import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S003C03

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S003C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 6815789 widths0 = 169 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 6815789 6848557).card = 169 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 6815789 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 6815789 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 6815789 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 6848557 widths1 = 182 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 6848557 6881325).card = 182 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 6848557 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 6848557 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 6848557 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 6881325 widths2 = 166 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 6881325 6914093).card = 166 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 6881325 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 6881325 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 6881325 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 6914093 widths3 = 192 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 6914093 6946861).card = 192 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 6914093 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 6914093 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 6914093 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 6815789 6881325).card = 351 := by
  simpa using combineTwinPrimeSegments (by decide : 6815789 ≤ 6848557)
    (by decide : 6848557 ≤ 6881325) block0 block1

theorem join_0_1 : (twinPrimeSegment 6881325 6946861).card = 358 := by
  simpa using combineTwinPrimeSegments (by decide : 6881325 ≤ 6914093)
    (by decide : 6914093 ≤ 6946861) block2 block3

theorem join_1_0 : (twinPrimeSegment 6815789 6946861).card = 709 := by
  simpa using combineTwinPrimeSegments (by decide : 6815789 ≤ 6881325)
    (by decide : 6881325 ≤ 6946861) join_0_0 join_0_1

theorem total : (twinPrimeSegment 6815789 6946861).card = 709 := join_1_0

end S003C04
end Sude.GeneratedTwinScan
