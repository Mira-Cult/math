import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S002C02

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S002C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 4587565 widths0 = 177 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 4587565 4620333).card = 177 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 4587565 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 4587565 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 4587565 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 4620333 widths1 = 187 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 4620333 4653101).card = 187 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 4620333 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 4620333 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 4620333 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 4653101 widths2 = 189 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 4653101 4685869).card = 189 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 4653101 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 4653101 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 4653101 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 4685869 widths3 = 184 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 4685869 4718637).card = 184 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 4685869 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 4685869 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 4685869 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 4587565 4653101).card = 364 := by
  simpa using combineTwinPrimeSegments (by decide : 4587565 ≤ 4620333)
    (by decide : 4620333 ≤ 4653101) block0 block1

theorem join_0_1 : (twinPrimeSegment 4653101 4718637).card = 373 := by
  simpa using combineTwinPrimeSegments (by decide : 4653101 ≤ 4685869)
    (by decide : 4685869 ≤ 4718637) block2 block3

theorem join_1_0 : (twinPrimeSegment 4587565 4718637).card = 737 := by
  simpa using combineTwinPrimeSegments (by decide : 4587565 ≤ 4653101)
    (by decide : 4653101 ≤ 4718637) join_0_0 join_0_1

theorem total : (twinPrimeSegment 4587565 4718637).card = 737 := join_1_0

end S002C03
end Sude.GeneratedTwinScan
