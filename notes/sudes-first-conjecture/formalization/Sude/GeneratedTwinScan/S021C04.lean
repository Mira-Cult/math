import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S021C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 44564525 widths0 = 143 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 44564525 44597293).card = 143 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 44564525 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 44597293 widths1 = 146 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 44597293 44630061).card = 146 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 44597293 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 44630061 widths2 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 44630061 44662829).card = 137 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 44630061 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 44662829 widths3 = 145 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 44662829 44695597).card = 145 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 44662829 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 44564525 44630061).card = 289 := by
  simpa using combineTwinPrimeSegments (by decide : 44564525 ≤ 44597293)
    (by decide : 44597293 ≤ 44630061) block0 block1

theorem join_0_1 : (twinPrimeSegment 44630061 44695597).card = 282 := by
  simpa using combineTwinPrimeSegments (by decide : 44630061 ≤ 44662829)
    (by decide : 44662829 ≤ 44695597) block2 block3

theorem join_1_0 : (twinPrimeSegment 44564525 44695597).card = 571 := by
  simpa using combineTwinPrimeSegments (by decide : 44564525 ≤ 44630061)
    (by decide : 44630061 ≤ 44695597) join_0_0 join_0_1

theorem total : (twinPrimeSegment 44564525 44695597).card = 571 := join_1_0

end S021C04
end Sude.GeneratedTwinScan
