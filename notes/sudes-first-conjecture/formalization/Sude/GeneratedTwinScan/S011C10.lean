import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S011C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 24379437 widths0 = 134 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 24379437 24412205).card = 134 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 24379437 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 24379437 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 24379437 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 24412205 widths1 = 141 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 24412205 24444973).card = 141 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 24412205 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 24412205 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 24412205 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 24444973 widths2 = 143 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 24444973 24477741).card = 143 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 24444973 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 24444973 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 24444973 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 24477741 widths3 = 149 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 24477741 24510509).card = 149 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 24477741 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 24477741 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 24477741 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 24379437 24444973).card = 275 := by
  simpa using combineTwinPrimeSegments (by decide : 24379437 ≤ 24412205)
    (by decide : 24412205 ≤ 24444973) block0 block1

theorem join_0_1 : (twinPrimeSegment 24444973 24510509).card = 292 := by
  simpa using combineTwinPrimeSegments (by decide : 24444973 ≤ 24477741)
    (by decide : 24477741 ≤ 24510509) block2 block3

theorem join_1_0 : (twinPrimeSegment 24379437 24510509).card = 567 := by
  simpa using combineTwinPrimeSegments (by decide : 24379437 ≤ 24444973)
    (by decide : 24444973 ≤ 24510509) join_0_0 join_0_1

theorem total : (twinPrimeSegment 24379437 24510509).card = 567 := join_1_0

end S011C10
end Sude.GeneratedTwinScan
