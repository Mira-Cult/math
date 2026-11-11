import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S002C01

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S002C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 4456493 widths0 = 195 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 4456493 4489261).card = 195 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 4456493 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 4456493 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 4456493 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 4489261 widths1 = 177 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 4489261 4522029).card = 177 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 4489261 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 4489261 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 4489261 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 4522029 widths2 = 174 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 4522029 4554797).card = 174 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 4522029 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 4522029 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 4522029 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 4554797 widths3 = 180 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 4554797 4587565).card = 180 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 4554797 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 4554797 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 4554797 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 4456493 4522029).card = 372 := by
  simpa using combineTwinPrimeSegments (by decide : 4456493 ≤ 4489261)
    (by decide : 4489261 ≤ 4522029) block0 block1

theorem join_0_1 : (twinPrimeSegment 4522029 4587565).card = 354 := by
  simpa using combineTwinPrimeSegments (by decide : 4522029 ≤ 4554797)
    (by decide : 4554797 ≤ 4587565) block2 block3

theorem join_1_0 : (twinPrimeSegment 4456493 4587565).card = 726 := by
  simpa using combineTwinPrimeSegments (by decide : 4456493 ≤ 4522029)
    (by decide : 4522029 ≤ 4587565) join_0_0 join_0_1

theorem total : (twinPrimeSegment 4456493 4587565).card = 726 := join_1_0

end S002C02
end Sude.GeneratedTwinScan
