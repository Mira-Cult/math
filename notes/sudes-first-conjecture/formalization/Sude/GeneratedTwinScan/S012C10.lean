import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S012C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 26476589 widths0 = 144 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 26476589 26509357).card = 144 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 26476589 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 26476589 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 26476589 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 26509357 widths1 = 150 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 26509357 26542125).card = 150 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 26509357 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 26509357 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 26509357 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 26542125 widths2 = 155 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 26542125 26574893).card = 155 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 26542125 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 26542125 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 26542125 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 26574893 widths3 = 141 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 26574893 26607661).card = 141 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 26574893 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 26574893 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 26574893 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 26476589 26542125).card = 294 := by
  simpa using combineTwinPrimeSegments (by decide : 26476589 ≤ 26509357)
    (by decide : 26509357 ≤ 26542125) block0 block1

theorem join_0_1 : (twinPrimeSegment 26542125 26607661).card = 296 := by
  simpa using combineTwinPrimeSegments (by decide : 26542125 ≤ 26574893)
    (by decide : 26574893 ≤ 26607661) block2 block3

theorem join_1_0 : (twinPrimeSegment 26476589 26607661).card = 590 := by
  simpa using combineTwinPrimeSegments (by decide : 26476589 ≤ 26542125)
    (by decide : 26542125 ≤ 26607661) join_0_0 join_0_1

theorem total : (twinPrimeSegment 26476589 26607661).card = 590 := join_1_0

end S012C10
end Sude.GeneratedTwinScan
