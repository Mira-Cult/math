import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S258C09

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S258C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 542375981 widths0 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 542375981 542408749).card = 117 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 542375981 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 542375981 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 542375981 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 542408749 widths1 = 83 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 542408749 542441517).card = 83 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 542408749 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 542408749 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 542408749 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 542441517 widths2 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 542441517 542474285).card = 99 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 542441517 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 542441517 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 542441517 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 542474285 widths3 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 542474285 542507053).card = 110 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 542474285 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 542474285 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 542474285 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 542375981 542441517).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 542375981 ≤ 542408749)
    (by decide : 542408749 ≤ 542441517) block0 block1

theorem join_0_1 : (twinPrimeSegment 542441517 542507053).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 542441517 ≤ 542474285)
    (by decide : 542474285 ≤ 542507053) block2 block3

theorem join_1_0 : (twinPrimeSegment 542375981 542507053).card = 409 := by
  simpa using combineTwinPrimeSegments (by decide : 542375981 ≤ 542441517)
    (by decide : 542441517 ≤ 542507053) join_0_0 join_0_1

theorem total : (twinPrimeSegment 542375981 542507053).card = 409 := join_1_0

end S258C10
end Sude.GeneratedTwinScan
