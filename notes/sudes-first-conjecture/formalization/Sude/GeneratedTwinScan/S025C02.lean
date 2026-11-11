import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S025C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 52690989 widths0 = 145 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 52690989 52723757).card = 145 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 52690989 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 52723757 widths1 = 137 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 52723757 52756525).card = 137 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 52723757 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 52756525 widths2 = 145 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 52756525 52789293).card = 145 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 52756525 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 52789293 widths3 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 52789293 52822061).card = 134 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 52789293 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 52690989 52756525).card = 282 := by
  simpa using combineTwinPrimeSegments (by decide : 52690989 ≤ 52723757)
    (by decide : 52723757 ≤ 52756525) block0 block1

theorem join_0_1 : (twinPrimeSegment 52756525 52822061).card = 279 := by
  simpa using combineTwinPrimeSegments (by decide : 52756525 ≤ 52789293)
    (by decide : 52789293 ≤ 52822061) block2 block3

theorem join_1_0 : (twinPrimeSegment 52690989 52822061).card = 561 := by
  simpa using combineTwinPrimeSegments (by decide : 52690989 ≤ 52756525)
    (by decide : 52756525 ≤ 52822061) join_0_0 join_0_1

theorem total : (twinPrimeSegment 52690989 52822061).card = 561 := join_1_0

end S025C02
end Sude.GeneratedTwinScan
