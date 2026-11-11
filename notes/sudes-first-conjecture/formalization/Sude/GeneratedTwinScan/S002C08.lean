import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S002C07

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S002C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 5242925 widths0 = 183 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 5242925 5275693).card = 183 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 5242925 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 5242925 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 5242925 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 5275693 widths1 = 176 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 5275693 5308461).card = 176 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 5275693 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 5275693 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 5275693 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 5308461 widths2 = 181 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 5308461 5341229).card = 181 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 5308461 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 5308461 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 5308461 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 5341229 widths3 = 170 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 5341229 5373997).card = 170 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 5341229 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 5341229 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 5341229 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 5242925 5308461).card = 359 := by
  simpa using combineTwinPrimeSegments (by decide : 5242925 ≤ 5275693)
    (by decide : 5275693 ≤ 5308461) block0 block1

theorem join_0_1 : (twinPrimeSegment 5308461 5373997).card = 351 := by
  simpa using combineTwinPrimeSegments (by decide : 5308461 ≤ 5341229)
    (by decide : 5341229 ≤ 5373997) block2 block3

theorem join_1_0 : (twinPrimeSegment 5242925 5373997).card = 710 := by
  simpa using combineTwinPrimeSegments (by decide : 5242925 ≤ 5308461)
    (by decide : 5308461 ≤ 5373997) join_0_0 join_0_1

theorem total : (twinPrimeSegment 5242925 5373997).card = 710 := join_1_0

end S002C08
end Sude.GeneratedTwinScan
