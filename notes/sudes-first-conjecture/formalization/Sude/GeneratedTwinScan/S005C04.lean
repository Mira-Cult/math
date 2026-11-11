import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.GeneratedTwinScan.S005C03

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S005C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : activeStreamingTwinScan finiteTwinCheckedBase 11010093 widths0 = 148 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 11010093 11042861).card = 148 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 11010093 widths0).symm.trans checked0
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 11010093 widths0).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 11010093 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : activeStreamingTwinScan finiteTwinCheckedBase 11042861 widths1 = 176 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 11042861 11075629).card = 176 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 11042861 widths1).symm.trans checked1
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 11042861 widths1).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 11042861 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : activeStreamingTwinScan finiteTwinCheckedBase 11075629 widths2 = 158 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 11075629 11108397).card = 158 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 11075629 widths2).symm.trans checked2
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 11075629 widths2).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 11075629 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : activeStreamingTwinScan finiteTwinCheckedBase 11108397 widths3 = 178 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 11108397 11141165).card = 178 := by
  have hs := (activeStreamingTwinScan_eq finiteTwinCheckedBase 11108397 widths3).symm.trans checked3
  have hb := (streamingTwinScan_eq finiteTwinCheckedBase 11108397 widths3).symm.trans hs
  have h := twinBitsetCountScan_spec finiteTwinCheckedBase 32768 11108397 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [hb] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 11010093 11075629).card = 324 := by
  simpa using combineTwinPrimeSegments (by decide : 11010093 ≤ 11042861)
    (by decide : 11042861 ≤ 11075629) block0 block1

theorem join_0_1 : (twinPrimeSegment 11075629 11141165).card = 336 := by
  simpa using combineTwinPrimeSegments (by decide : 11075629 ≤ 11108397)
    (by decide : 11108397 ≤ 11141165) block2 block3

theorem join_1_0 : (twinPrimeSegment 11010093 11141165).card = 660 := by
  simpa using combineTwinPrimeSegments (by decide : 11010093 ≤ 11075629)
    (by decide : 11075629 ≤ 11141165) join_0_0 join_0_1

theorem total : (twinPrimeSegment 11010093 11141165).card = 660 := join_1_0

end S005C04
end Sude.GeneratedTwinScan
