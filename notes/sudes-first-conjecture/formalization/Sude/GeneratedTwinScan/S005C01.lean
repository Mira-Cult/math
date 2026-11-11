import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S005C00

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S005C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 10616877 widths0 = 187 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 10616877 10649645).card = 187 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 10616877 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 10616877 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 10616877 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 10649645 widths1 = 158 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 10649645 10682413).card = 158 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 10649645 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 10649645 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 10649645 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 10682413 widths2 = 177 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 10682413 10715181).card = 177 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 10682413 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 10682413 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 10682413 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 10715181 widths3 = 169 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 10715181 10747949).card = 169 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 10715181 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 10715181 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 10715181 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 10616877 10682413).card = 345 := by
  simpa using combineTwinPrimeSegments (by decide : 10616877 ≤ 10649645)
    (by decide : 10649645 ≤ 10682413) block0 block1

theorem join_0_1 : (twinPrimeSegment 10682413 10747949).card = 346 := by
  simpa using combineTwinPrimeSegments (by decide : 10682413 ≤ 10715181)
    (by decide : 10715181 ≤ 10747949) block2 block3

theorem join_1_0 : (twinPrimeSegment 10616877 10747949).card = 691 := by
  simpa using combineTwinPrimeSegments (by decide : 10616877 ≤ 10682413)
    (by decide : 10682413 ≤ 10747949) join_0_0 join_0_1

theorem total : (twinPrimeSegment 10616877 10747949).card = 691 := join_1_0

end S005C01
end Sude.GeneratedTwinScan
