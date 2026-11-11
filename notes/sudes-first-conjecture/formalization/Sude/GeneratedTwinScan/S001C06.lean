import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S001C05

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S001C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 2883629 widths0 = 168 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 2883629 2916397).card = 168 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 2883629 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 2883629 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 2883629 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 2916397 widths1 = 192 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 2916397 2949165).card = 192 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 2916397 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 2916397 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 2916397 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 2949165 widths2 = 217 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 2949165 2981933).card = 217 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 2949165 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 2949165 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 2949165 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 2981933 widths3 = 200 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 2981933 3014701).card = 200 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 2981933 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 2981933 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 2981933 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 2883629 2949165).card = 360 := by
  simpa using combineTwinPrimeSegments (by decide : 2883629 ≤ 2916397)
    (by decide : 2916397 ≤ 2949165) block0 block1

theorem join_0_1 : (twinPrimeSegment 2949165 3014701).card = 417 := by
  simpa using combineTwinPrimeSegments (by decide : 2949165 ≤ 2981933)
    (by decide : 2981933 ≤ 3014701) block2 block3

theorem join_1_0 : (twinPrimeSegment 2883629 3014701).card = 777 := by
  simpa using combineTwinPrimeSegments (by decide : 2883629 ≤ 2949165)
    (by decide : 2949165 ≤ 3014701) join_0_0 join_0_1

theorem total : (twinPrimeSegment 2883629 3014701).card = 777 := join_1_0

end S001C06
end Sude.GeneratedTwinScan
