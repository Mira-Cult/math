import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S007C03

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S007C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 15204397 widths0 = 153 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 15204397 15237165).card = 153 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 15204397 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 15204397 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 15204397 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 15237165 widths1 = 165 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 15237165 15269933).card = 165 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 15237165 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 15237165 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 15237165 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 15269933 widths2 = 152 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 15269933 15302701).card = 152 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 15269933 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 15269933 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 15269933 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 15302701 widths3 = 176 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 15302701 15335469).card = 176 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 15302701 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 15302701 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 15302701 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 15204397 15269933).card = 318 := by
  simpa using combineTwinPrimeSegments (by decide : 15204397 ≤ 15237165)
    (by decide : 15237165 ≤ 15269933) block0 block1

theorem join_0_1 : (twinPrimeSegment 15269933 15335469).card = 328 := by
  simpa using combineTwinPrimeSegments (by decide : 15269933 ≤ 15302701)
    (by decide : 15302701 ≤ 15335469) block2 block3

theorem join_1_0 : (twinPrimeSegment 15204397 15335469).card = 646 := by
  simpa using combineTwinPrimeSegments (by decide : 15204397 ≤ 15269933)
    (by decide : 15269933 ≤ 15335469) join_0_0 join_0_1

theorem total : (twinPrimeSegment 15204397 15335469).card = 646 := join_1_0

end S007C04
end Sude.GeneratedTwinScan
