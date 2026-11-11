import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S022C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 46923821 widths0 = 139 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 46923821 46956589).card = 139 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 46923821 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 46956589 widths1 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 46956589 46989357).card = 132 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 46956589 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 46989357 widths2 = 144 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 46989357 47022125).card = 144 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 46989357 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 47022125 widths3 = 140 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 47022125 47054893).card = 140 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 47022125 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 46923821 46989357).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 46923821 ≤ 46956589)
    (by decide : 46956589 ≤ 46989357) block0 block1

theorem join_0_1 : (twinPrimeSegment 46989357 47054893).card = 284 := by
  simpa using combineTwinPrimeSegments (by decide : 46989357 ≤ 47022125)
    (by decide : 47022125 ≤ 47054893) block2 block3

theorem join_1_0 : (twinPrimeSegment 46923821 47054893).card = 555 := by
  simpa using combineTwinPrimeSegments (by decide : 46923821 ≤ 46989357)
    (by decide : 46989357 ≤ 47054893) join_0_0 join_0_1

theorem total : (twinPrimeSegment 46923821 47054893).card = 555 := join_1_0

end S022C06
end Sude.GeneratedTwinScan
