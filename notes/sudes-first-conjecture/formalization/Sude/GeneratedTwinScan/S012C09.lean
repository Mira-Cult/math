import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S012C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 26345517 widths0 = 147 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 26345517 26378285).card = 147 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 26345517 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 26345517 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 26345517 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 26378285 widths1 = 154 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 26378285 26411053).card = 154 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 26378285 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 26378285 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 26378285 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 26411053 widths2 = 158 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 26411053 26443821).card = 158 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 26411053 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 26411053 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 26411053 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 26443821 widths3 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 26443821 26476589).card = 135 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 26443821 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 26443821 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 26443821 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 26345517 26411053).card = 301 := by
  simpa using combineTwinPrimeSegments (by decide : 26345517 ≤ 26378285)
    (by decide : 26378285 ≤ 26411053) block0 block1

theorem join_0_1 : (twinPrimeSegment 26411053 26476589).card = 293 := by
  simpa using combineTwinPrimeSegments (by decide : 26411053 ≤ 26443821)
    (by decide : 26443821 ≤ 26476589) block2 block3

theorem join_1_0 : (twinPrimeSegment 26345517 26476589).card = 594 := by
  simpa using combineTwinPrimeSegments (by decide : 26345517 ≤ 26411053)
    (by decide : 26411053 ≤ 26476589) join_0_0 join_0_1

theorem total : (twinPrimeSegment 26345517 26476589).card = 594 := join_1_0

end S012C09
end Sude.GeneratedTwinScan
