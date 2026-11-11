import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S012C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 27000877 widths0 = 152 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 27000877 27033645).card = 152 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 27000877 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 27000877 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 27000877 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 27033645 widths1 = 146 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 27033645 27066413).card = 146 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 27033645 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 27033645 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 27033645 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 27066413 widths2 = 165 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 27066413 27099181).card = 165 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 27066413 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 27066413 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 27066413 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 27099181 widths3 = 141 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 27099181 27131949).card = 141 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 27099181 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 27099181 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 27099181 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 27000877 27066413).card = 298 := by
  simpa using combineTwinPrimeSegments (by decide : 27000877 ≤ 27033645)
    (by decide : 27033645 ≤ 27066413) block0 block1

theorem join_0_1 : (twinPrimeSegment 27066413 27131949).card = 306 := by
  simpa using combineTwinPrimeSegments (by decide : 27066413 ≤ 27099181)
    (by decide : 27099181 ≤ 27131949) block2 block3

theorem join_1_0 : (twinPrimeSegment 27000877 27131949).card = 604 := by
  simpa using combineTwinPrimeSegments (by decide : 27000877 ≤ 27066413)
    (by decide : 27066413 ≤ 27131949) join_0_0 join_0_1

theorem total : (twinPrimeSegment 27000877 27131949).card = 604 := join_1_0

end S012C14
end Sude.GeneratedTwinScan
