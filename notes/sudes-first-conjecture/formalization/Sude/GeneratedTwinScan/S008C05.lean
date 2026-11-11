import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S008C04

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S008C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 17432621 widths0 = 158 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 17432621 17465389).card = 158 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 17432621 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 17432621 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 17432621 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 17465389 widths1 = 160 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 17465389 17498157).card = 160 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 17465389 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 17465389 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 17465389 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 17498157 widths2 = 159 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 17498157 17530925).card = 159 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 17498157 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 17498157 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 17498157 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 17530925 widths3 = 173 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 17530925 17563693).card = 173 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 17530925 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 17530925 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 17530925 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 17432621 17498157).card = 318 := by
  simpa using combineTwinPrimeSegments (by decide : 17432621 ≤ 17465389)
    (by decide : 17465389 ≤ 17498157) block0 block1

theorem join_0_1 : (twinPrimeSegment 17498157 17563693).card = 332 := by
  simpa using combineTwinPrimeSegments (by decide : 17498157 ≤ 17530925)
    (by decide : 17530925 ≤ 17563693) block2 block3

theorem join_1_0 : (twinPrimeSegment 17432621 17563693).card = 650 := by
  simpa using combineTwinPrimeSegments (by decide : 17432621 ≤ 17498157)
    (by decide : 17498157 ≤ 17563693) join_0_0 join_0_1

theorem total : (twinPrimeSegment 17432621 17563693).card = 650 := join_1_0

end S008C05
end Sude.GeneratedTwinScan
