import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S258C06

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S258C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 541982765 widths0 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 541982765 542015533).card = 107 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 541982765 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 541982765 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 541982765 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 542015533 widths1 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 542015533 542048301).card = 114 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 542015533 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 542015533 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 542015533 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 542048301 widths2 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 542048301 542081069).card = 107 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 542048301 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 542048301 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 542048301 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 542081069 widths3 = 88 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 542081069 542113837).card = 88 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 542081069 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 542081069 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 542081069 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 541982765 542048301).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 541982765 ≤ 542015533)
    (by decide : 542015533 ≤ 542048301) block0 block1

theorem join_0_1 : (twinPrimeSegment 542048301 542113837).card = 195 := by
  simpa using combineTwinPrimeSegments (by decide : 542048301 ≤ 542081069)
    (by decide : 542081069 ≤ 542113837) block2 block3

theorem join_1_0 : (twinPrimeSegment 541982765 542113837).card = 416 := by
  simpa using combineTwinPrimeSegments (by decide : 541982765 ≤ 542048301)
    (by decide : 542048301 ≤ 542113837) join_0_0 join_0_1

theorem total : (twinPrimeSegment 541982765 542113837).card = 416 := join_1_0

end S258C07
end Sude.GeneratedTwinScan
