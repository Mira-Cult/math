import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S258C12

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S258C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 542769197 widths0 = 91 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 542769197 542801965).card = 91 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 542769197 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 542769197 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 542769197 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 542801965 widths1 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 542801965 542834733).card = 109 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 542801965 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 542801965 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 542801965 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 542834733 widths2 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 542834733 542867501).card = 114 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 542834733 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 542834733 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 542834733 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 542867501 widths3 = 94 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 542867501 542900269).card = 94 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 542867501 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 542867501 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 542867501 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 542769197 542834733).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 542769197 ≤ 542801965)
    (by decide : 542801965 ≤ 542834733) block0 block1

theorem join_0_1 : (twinPrimeSegment 542834733 542900269).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 542834733 ≤ 542867501)
    (by decide : 542867501 ≤ 542900269) block2 block3

theorem join_1_0 : (twinPrimeSegment 542769197 542900269).card = 408 := by
  simpa using combineTwinPrimeSegments (by decide : 542769197 ≤ 542834733)
    (by decide : 542834733 ≤ 542900269) join_0_0 join_0_1

theorem total : (twinPrimeSegment 542769197 542900269).card = 408 := join_1_0

end S258C13
end Sude.GeneratedTwinScan
