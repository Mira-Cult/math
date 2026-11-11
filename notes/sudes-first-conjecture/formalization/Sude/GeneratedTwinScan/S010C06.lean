import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S010C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 21757997 widths0 = 142 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 21757997 21790765).card = 142 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 21757997 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 21757997 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 21757997 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 21790765 widths1 = 146 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 21790765 21823533).card = 146 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 21790765 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 21790765 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 21790765 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 21823533 widths2 = 161 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 21823533 21856301).card = 161 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 21823533 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 21823533 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 21823533 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 21856301 widths3 = 148 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 21856301 21889069).card = 148 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 21856301 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 21856301 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 21856301 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 21757997 21823533).card = 288 := by
  simpa using combineTwinPrimeSegments (by decide : 21757997 ≤ 21790765)
    (by decide : 21790765 ≤ 21823533) block0 block1

theorem join_0_1 : (twinPrimeSegment 21823533 21889069).card = 309 := by
  simpa using combineTwinPrimeSegments (by decide : 21823533 ≤ 21856301)
    (by decide : 21856301 ≤ 21889069) block2 block3

theorem join_1_0 : (twinPrimeSegment 21757997 21889069).card = 597 := by
  simpa using combineTwinPrimeSegments (by decide : 21757997 ≤ 21823533)
    (by decide : 21823533 ≤ 21889069) join_0_0 join_0_1

theorem total : (twinPrimeSegment 21757997 21889069).card = 597 := join_1_0

end S010C06
end Sude.GeneratedTwinScan
