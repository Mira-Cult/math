import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S007C08

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S007C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 15859757 widths0 = 169 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 15859757 15892525).card = 169 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 15859757 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 15859757 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 15859757 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 15892525 widths1 = 153 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 15892525 15925293).card = 153 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 15892525 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 15892525 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 15892525 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 15925293 widths2 = 152 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 15925293 15958061).card = 152 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 15925293 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 15925293 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 15925293 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 15958061 widths3 = 158 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 15958061 15990829).card = 158 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 15958061 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 15958061 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 15958061 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 15859757 15925293).card = 322 := by
  simpa using combineTwinPrimeSegments (by decide : 15859757 ≤ 15892525)
    (by decide : 15892525 ≤ 15925293) block0 block1

theorem join_0_1 : (twinPrimeSegment 15925293 15990829).card = 310 := by
  simpa using combineTwinPrimeSegments (by decide : 15925293 ≤ 15958061)
    (by decide : 15958061 ≤ 15990829) block2 block3

theorem join_1_0 : (twinPrimeSegment 15859757 15990829).card = 632 := by
  simpa using combineTwinPrimeSegments (by decide : 15859757 ≤ 15925293)
    (by decide : 15925293 ≤ 15990829) join_0_0 join_0_1

theorem total : (twinPrimeSegment 15859757 15990829).card = 632 := join_1_0

end S007C09
end Sude.GeneratedTwinScan
