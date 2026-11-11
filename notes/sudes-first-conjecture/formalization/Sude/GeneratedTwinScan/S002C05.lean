import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S002C04

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S002C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 4849709 widths0 = 180 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 4849709 4882477).card = 180 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 4849709 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 4849709 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 4849709 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 4882477 widths1 = 195 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 4882477 4915245).card = 195 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 4882477 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 4882477 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 4882477 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 4915245 widths2 = 177 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 4915245 4948013).card = 177 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 4915245 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 4915245 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 4915245 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 4948013 widths3 = 183 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 4948013 4980781).card = 183 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 4948013 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 4948013 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 4948013 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 4849709 4915245).card = 375 := by
  simpa using combineTwinPrimeSegments (by decide : 4849709 ≤ 4882477)
    (by decide : 4882477 ≤ 4915245) block0 block1

theorem join_0_1 : (twinPrimeSegment 4915245 4980781).card = 360 := by
  simpa using combineTwinPrimeSegments (by decide : 4915245 ≤ 4948013)
    (by decide : 4948013 ≤ 4980781) block2 block3

theorem join_1_0 : (twinPrimeSegment 4849709 4980781).card = 735 := by
  simpa using combineTwinPrimeSegments (by decide : 4849709 ≤ 4915245)
    (by decide : 4915245 ≤ 4980781) join_0_0 join_0_1

theorem total : (twinPrimeSegment 4849709 4980781).card = 735 := join_1_0

end S002C05
end Sude.GeneratedTwinScan
