import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S012C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 25296941 widths0 = 149 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 25296941 25329709).card = 149 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 25296941 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 25296941 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 25296941 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 25329709 widths1 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 25329709 25362477).card = 130 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 25329709 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 25329709 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 25329709 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 25362477 widths2 = 146 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 25362477 25395245).card = 146 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 25362477 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 25362477 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 25362477 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 25395245 widths3 = 147 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 25395245 25428013).card = 147 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 25395245 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 25395245 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 25395245 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 25296941 25362477).card = 279 := by
  simpa using combineTwinPrimeSegments (by decide : 25296941 ≤ 25329709)
    (by decide : 25329709 ≤ 25362477) block0 block1

theorem join_0_1 : (twinPrimeSegment 25362477 25428013).card = 293 := by
  simpa using combineTwinPrimeSegments (by decide : 25362477 ≤ 25395245)
    (by decide : 25395245 ≤ 25428013) block2 block3

theorem join_1_0 : (twinPrimeSegment 25296941 25428013).card = 572 := by
  simpa using combineTwinPrimeSegments (by decide : 25296941 ≤ 25362477)
    (by decide : 25362477 ≤ 25428013) join_0_0 join_0_1

theorem total : (twinPrimeSegment 25296941 25428013).card = 572 := join_1_0

end S012C01
end Sude.GeneratedTwinScan
