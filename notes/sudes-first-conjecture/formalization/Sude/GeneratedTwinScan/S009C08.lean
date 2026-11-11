import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S009C07

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S009C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 19922989 widths0 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 19922989 19955757).card = 135 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 19922989 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 19922989 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 19922989 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 19955757 widths1 = 160 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 19955757 19988525).card = 160 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 19955757 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 19955757 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 19955757 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 19988525 widths2 = 161 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 19988525 20021293).card = 161 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 19988525 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 19988525 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 19988525 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 20021293 widths3 = 163 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 20021293 20054061).card = 163 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 20021293 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 20021293 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 20021293 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 19922989 19988525).card = 295 := by
  simpa using combineTwinPrimeSegments (by decide : 19922989 ≤ 19955757)
    (by decide : 19955757 ≤ 19988525) block0 block1

theorem join_0_1 : (twinPrimeSegment 19988525 20054061).card = 324 := by
  simpa using combineTwinPrimeSegments (by decide : 19988525 ≤ 20021293)
    (by decide : 20021293 ≤ 20054061) block2 block3

theorem join_1_0 : (twinPrimeSegment 19922989 20054061).card = 619 := by
  simpa using combineTwinPrimeSegments (by decide : 19922989 ≤ 19988525)
    (by decide : 19988525 ≤ 20054061) join_0_0 join_0_1

theorem total : (twinPrimeSegment 19922989 20054061).card = 619 := join_1_0

end S009C08
end Sude.GeneratedTwinScan
