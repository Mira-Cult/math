import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S000C07

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S000C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 1048621 widths0 = 223 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 1048621 1081389).card = 223 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 1048621 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 1048621 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 1048621 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 1081389 widths1 = 232 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 1081389 1114157).card = 232 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 1081389 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 1081389 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 1081389 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 1114157 widths2 = 233 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 1114157 1146925).card = 233 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 1114157 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 1114157 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 1114157 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 1146925 widths3 = 225 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 1146925 1179693).card = 225 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 1146925 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 1146925 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 1146925 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 1048621 1114157).card = 455 := by
  simpa using combineTwinPrimeSegments (by decide : 1048621 ≤ 1081389)
    (by decide : 1081389 ≤ 1114157) block0 block1

theorem join_0_1 : (twinPrimeSegment 1114157 1179693).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 1114157 ≤ 1146925)
    (by decide : 1146925 ≤ 1179693) block2 block3

theorem join_1_0 : (twinPrimeSegment 1048621 1179693).card = 913 := by
  simpa using combineTwinPrimeSegments (by decide : 1048621 ≤ 1114157)
    (by decide : 1114157 ≤ 1179693) join_0_0 join_0_1

theorem total : (twinPrimeSegment 1048621 1179693).card = 913 := join_1_0

end S000C08
end Sude.GeneratedTwinScan
