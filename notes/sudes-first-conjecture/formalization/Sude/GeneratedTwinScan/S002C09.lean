import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S002C08

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S002C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 5373997 widths0 = 190 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 5373997 5406765).card = 190 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 5373997 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 5373997 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 5373997 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 5406765 widths1 = 175 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 5406765 5439533).card = 175 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 5406765 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 5406765 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 5406765 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 5439533 widths2 = 205 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 5439533 5472301).card = 205 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 5439533 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 5439533 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 5439533 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 5472301 widths3 = 172 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 5472301 5505069).card = 172 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 5472301 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 5472301 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 5472301 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 5373997 5439533).card = 365 := by
  simpa using combineTwinPrimeSegments (by decide : 5373997 ≤ 5406765)
    (by decide : 5406765 ≤ 5439533) block0 block1

theorem join_0_1 : (twinPrimeSegment 5439533 5505069).card = 377 := by
  simpa using combineTwinPrimeSegments (by decide : 5439533 ≤ 5472301)
    (by decide : 5472301 ≤ 5505069) block2 block3

theorem join_1_0 : (twinPrimeSegment 5373997 5505069).card = 742 := by
  simpa using combineTwinPrimeSegments (by decide : 5373997 ≤ 5439533)
    (by decide : 5439533 ≤ 5505069) join_0_0 join_0_1

theorem total : (twinPrimeSegment 5373997 5505069).card = 742 := join_1_0

end S002C09
end Sude.GeneratedTwinScan
