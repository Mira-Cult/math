import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S023C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 48365613 widths0 = 134 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 48365613 48398381).card = 134 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 48365613 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 48398381 widths1 = 138 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 48398381 48431149).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 48398381 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 48431149 widths2 = 149 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 48431149 48463917).card = 149 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 48431149 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 48463917 widths3 = 143 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 48463917 48496685).card = 143 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 48463917 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 48365613 48431149).card = 272 := by
  simpa using combineTwinPrimeSegments (by decide : 48365613 ≤ 48398381)
    (by decide : 48398381 ≤ 48431149) block0 block1

theorem join_0_1 : (twinPrimeSegment 48431149 48496685).card = 292 := by
  simpa using combineTwinPrimeSegments (by decide : 48431149 ≤ 48463917)
    (by decide : 48463917 ≤ 48496685) block2 block3

theorem join_1_0 : (twinPrimeSegment 48365613 48496685).card = 564 := by
  simpa using combineTwinPrimeSegments (by decide : 48365613 ≤ 48431149)
    (by decide : 48431149 ≤ 48496685) join_0_0 join_0_1

theorem total : (twinPrimeSegment 48365613 48496685).card = 564 := join_1_0

end S023C01
end Sude.GeneratedTwinScan
