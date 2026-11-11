import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S258C07

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S258C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 542113837 widths0 = 96 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 542113837 542146605).card = 96 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 542113837 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 542113837 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 542113837 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 542146605 widths1 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 542146605 542179373).card = 118 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 542146605 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 542146605 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 542146605 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 542179373 widths2 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 542179373 542212141).card = 120 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 542179373 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 542179373 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 542179373 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 542212141 widths3 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 542212141 542244909).card = 107 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 542212141 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 542212141 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 542212141 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 542113837 542179373).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 542113837 ≤ 542146605)
    (by decide : 542146605 ≤ 542179373) block0 block1

theorem join_0_1 : (twinPrimeSegment 542179373 542244909).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 542179373 ≤ 542212141)
    (by decide : 542212141 ≤ 542244909) block2 block3

theorem join_1_0 : (twinPrimeSegment 542113837 542244909).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 542113837 ≤ 542179373)
    (by decide : 542179373 ≤ 542244909) join_0_0 join_0_1

theorem total : (twinPrimeSegment 542113837 542244909).card = 441 := join_1_0

end S258C08
end Sude.GeneratedTwinScan
