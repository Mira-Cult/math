import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S008C08

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S008C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 17956909 widths0 = 167 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 17956909 17989677).card = 167 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 17956909 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 17956909 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 17956909 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 17989677 widths1 = 148 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 17989677 18022445).card = 148 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 17989677 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 17989677 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 17989677 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 18022445 widths2 = 144 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 18022445 18055213).card = 144 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 18022445 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 18022445 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 18022445 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 18055213 widths3 = 146 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 18055213 18087981).card = 146 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 18055213 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 18055213 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 18055213 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 17956909 18022445).card = 315 := by
  simpa using combineTwinPrimeSegments (by decide : 17956909 ≤ 17989677)
    (by decide : 17989677 ≤ 18022445) block0 block1

theorem join_0_1 : (twinPrimeSegment 18022445 18087981).card = 290 := by
  simpa using combineTwinPrimeSegments (by decide : 18022445 ≤ 18055213)
    (by decide : 18055213 ≤ 18087981) block2 block3

theorem join_1_0 : (twinPrimeSegment 17956909 18087981).card = 605 := by
  simpa using combineTwinPrimeSegments (by decide : 17956909 ≤ 18022445)
    (by decide : 18022445 ≤ 18087981) join_0_0 join_0_1

theorem total : (twinPrimeSegment 17956909 18087981).card = 605 := join_1_0

end S008C09
end Sude.GeneratedTwinScan
