import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S258C10

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S258C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 542507053 widths0 = 90 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 542507053 542539821).card = 90 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 542507053 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 542507053 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 542507053 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 542539821 widths1 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 542539821 542572589).card = 107 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 542539821 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 542539821 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 542539821 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 542572589 widths2 = 97 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 542572589 542605357).card = 97 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 542572589 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 542572589 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 542572589 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 542605357 widths3 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 542605357 542638125).card = 115 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 542605357 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 542605357 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 542605357 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 542507053 542572589).card = 197 := by
  simpa using combineTwinPrimeSegments (by decide : 542507053 ≤ 542539821)
    (by decide : 542539821 ≤ 542572589) block0 block1

theorem join_0_1 : (twinPrimeSegment 542572589 542638125).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 542572589 ≤ 542605357)
    (by decide : 542605357 ≤ 542638125) block2 block3

theorem join_1_0 : (twinPrimeSegment 542507053 542638125).card = 409 := by
  simpa using combineTwinPrimeSegments (by decide : 542507053 ≤ 542572589)
    (by decide : 542572589 ≤ 542638125) join_0_0 join_0_1

theorem total : (twinPrimeSegment 542507053 542638125).card = 409 := join_1_0

end S258C11
end Sude.GeneratedTwinScan
