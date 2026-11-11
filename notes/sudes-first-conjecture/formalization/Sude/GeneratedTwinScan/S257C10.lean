import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S257C09

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S257C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 540278829 widths0 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 540278829 540311597).card = 107 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 540278829 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 540278829 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 540278829 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 540311597 widths1 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 540311597 540344365).card = 115 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 540311597 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 540311597 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 540311597 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 540344365 widths2 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 540344365 540377133).card = 103 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 540344365 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 540344365 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 540344365 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 540377133 widths3 = 90 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 540377133 540409901).card = 90 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 540377133 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 540377133 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 540377133 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 540278829 540344365).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 540278829 ≤ 540311597)
    (by decide : 540311597 ≤ 540344365) block0 block1

theorem join_0_1 : (twinPrimeSegment 540344365 540409901).card = 193 := by
  simpa using combineTwinPrimeSegments (by decide : 540344365 ≤ 540377133)
    (by decide : 540377133 ≤ 540409901) block2 block3

theorem join_1_0 : (twinPrimeSegment 540278829 540409901).card = 415 := by
  simpa using combineTwinPrimeSegments (by decide : 540278829 ≤ 540344365)
    (by decide : 540344365 ≤ 540409901) join_0_0 join_0_1

theorem total : (twinPrimeSegment 540278829 540409901).card = 415 := join_1_0

end S257C10
end Sude.GeneratedTwinScan
