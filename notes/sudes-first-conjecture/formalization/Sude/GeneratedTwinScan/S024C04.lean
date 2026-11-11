import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S024C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 50855981 widths0 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 50855981 50888749).card = 124 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 50855981 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 50888749 widths1 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 50888749 50921517).card = 130 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 50888749 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 50921517 widths2 = 141 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 50921517 50954285).card = 141 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 50921517 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 50954285 widths3 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 50954285 50987053).card = 135 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 50954285 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 50855981 50921517).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 50855981 ≤ 50888749)
    (by decide : 50888749 ≤ 50921517) block0 block1

theorem join_0_1 : (twinPrimeSegment 50921517 50987053).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 50921517 ≤ 50954285)
    (by decide : 50954285 ≤ 50987053) block2 block3

theorem join_1_0 : (twinPrimeSegment 50855981 50987053).card = 530 := by
  simpa using combineTwinPrimeSegments (by decide : 50855981 ≤ 50921517)
    (by decide : 50921517 ≤ 50987053) join_0_0 join_0_1

theorem total : (twinPrimeSegment 50855981 50987053).card = 530 := join_1_0

end S024C04
end Sude.GeneratedTwinScan
