import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S014C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 29360173 widths0 = 151 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 29360173 29392941).card = 151 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 29360173 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 29360173 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 29360173 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 29392941 widths1 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 29392941 29425709).card = 133 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 29392941 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 29392941 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 29392941 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 29425709 widths2 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 29425709 29458477).card = 137 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 29425709 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 29425709 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 29425709 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 29458477 widths3 = 148 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 29458477 29491245).card = 148 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 29458477 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 29458477 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 29458477 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 29360173 29425709).card = 284 := by
  simpa using combineTwinPrimeSegments (by decide : 29360173 ≤ 29392941)
    (by decide : 29392941 ≤ 29425709) block0 block1

theorem join_0_1 : (twinPrimeSegment 29425709 29491245).card = 285 := by
  simpa using combineTwinPrimeSegments (by decide : 29425709 ≤ 29458477)
    (by decide : 29458477 ≤ 29491245) block2 block3

theorem join_1_0 : (twinPrimeSegment 29360173 29491245).card = 569 := by
  simpa using combineTwinPrimeSegments (by decide : 29360173 ≤ 29425709)
    (by decide : 29425709 ≤ 29491245) join_0_0 join_0_1

theorem total : (twinPrimeSegment 29360173 29491245).card = 569 := join_1_0

end S014C00
end Sude.GeneratedTwinScan
