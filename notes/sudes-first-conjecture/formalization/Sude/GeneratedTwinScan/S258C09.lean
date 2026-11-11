import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S258C08

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S258C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 542244909 widths0 = 89 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 542244909 542277677).card = 89 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 542244909 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 542244909 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 542244909 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 542277677 widths1 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 542277677 542310445).card = 112 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 542277677 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 542277677 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 542277677 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 542310445 widths2 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 542310445 542343213).card = 115 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 542310445 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 542310445 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 542310445 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 542343213 widths3 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 542343213 542375981).card = 107 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 542343213 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 542343213 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 542343213 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 542244909 542310445).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 542244909 ≤ 542277677)
    (by decide : 542277677 ≤ 542310445) block0 block1

theorem join_0_1 : (twinPrimeSegment 542310445 542375981).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 542310445 ≤ 542343213)
    (by decide : 542343213 ≤ 542375981) block2 block3

theorem join_1_0 : (twinPrimeSegment 542244909 542375981).card = 423 := by
  simpa using combineTwinPrimeSegments (by decide : 542244909 ≤ 542310445)
    (by decide : 542310445 ≤ 542375981) join_0_0 join_0_1

theorem total : (twinPrimeSegment 542244909 542375981).card = 423 := join_1_0

end S258C09
end Sude.GeneratedTwinScan
