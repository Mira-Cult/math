import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S004C00

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S004C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 8519725 widths0 = 180 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 8519725 8552493).card = 180 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 8519725 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 8519725 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 8519725 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 8552493 widths1 = 184 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 8552493 8585261).card = 184 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 8552493 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 8552493 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 8552493 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 8585261 widths2 = 182 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 8585261 8618029).card = 182 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 8585261 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 8585261 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 8585261 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 8618029 widths3 = 179 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 8618029 8650797).card = 179 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 8618029 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 8618029 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 8618029 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 8519725 8585261).card = 364 := by
  simpa using combineTwinPrimeSegments (by decide : 8519725 ≤ 8552493)
    (by decide : 8552493 ≤ 8585261) block0 block1

theorem join_0_1 : (twinPrimeSegment 8585261 8650797).card = 361 := by
  simpa using combineTwinPrimeSegments (by decide : 8585261 ≤ 8618029)
    (by decide : 8618029 ≤ 8650797) block2 block3

theorem join_1_0 : (twinPrimeSegment 8519725 8650797).card = 725 := by
  simpa using combineTwinPrimeSegments (by decide : 8519725 ≤ 8585261)
    (by decide : 8585261 ≤ 8650797) join_0_0 join_0_1

theorem total : (twinPrimeSegment 8519725 8650797).card = 725 := join_1_0

end S004C01
end Sude.GeneratedTwinScan
