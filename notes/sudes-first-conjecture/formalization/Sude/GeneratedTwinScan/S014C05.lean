import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S014C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 30015533 widths0 = 161 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 30015533 30048301).card = 161 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 30015533 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 30015533 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 30015533 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 30048301 widths1 = 144 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 30048301 30081069).card = 144 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 30048301 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 30048301 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 30048301 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 30081069 widths2 = 138 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 30081069 30113837).card = 138 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 30081069 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 30081069 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 30081069 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 30113837 widths3 = 144 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 30113837 30146605).card = 144 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 30113837 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 30113837 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 30113837 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 30015533 30081069).card = 305 := by
  simpa using combineTwinPrimeSegments (by decide : 30015533 ≤ 30048301)
    (by decide : 30048301 ≤ 30081069) block0 block1

theorem join_0_1 : (twinPrimeSegment 30081069 30146605).card = 282 := by
  simpa using combineTwinPrimeSegments (by decide : 30081069 ≤ 30113837)
    (by decide : 30113837 ≤ 30146605) block2 block3

theorem join_1_0 : (twinPrimeSegment 30015533 30146605).card = 587 := by
  simpa using combineTwinPrimeSegments (by decide : 30015533 ≤ 30081069)
    (by decide : 30081069 ≤ 30146605) join_0_0 join_0_1

theorem total : (twinPrimeSegment 30015533 30146605).card = 587 := join_1_0

end S014C05
end Sude.GeneratedTwinScan
