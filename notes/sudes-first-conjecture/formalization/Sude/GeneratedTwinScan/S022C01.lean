import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S022C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 46268461 widths0 = 159 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 46268461 46301229).card = 159 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 46268461 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 46301229 widths1 = 144 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 46301229 46333997).card = 144 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 46301229 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 46333997 widths2 = 166 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 46333997 46366765).card = 166 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 46333997 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 46366765 widths3 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 46366765 46399533).card = 129 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 46366765 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 46268461 46333997).card = 303 := by
  simpa using combineTwinPrimeSegments (by decide : 46268461 ≤ 46301229)
    (by decide : 46301229 ≤ 46333997) block0 block1

theorem join_0_1 : (twinPrimeSegment 46333997 46399533).card = 295 := by
  simpa using combineTwinPrimeSegments (by decide : 46333997 ≤ 46366765)
    (by decide : 46366765 ≤ 46399533) block2 block3

theorem join_1_0 : (twinPrimeSegment 46268461 46399533).card = 598 := by
  simpa using combineTwinPrimeSegments (by decide : 46268461 ≤ 46333997)
    (by decide : 46333997 ≤ 46399533) join_0_0 join_0_1

theorem total : (twinPrimeSegment 46268461 46399533).card = 598 := join_1_0

end S022C01
end Sude.GeneratedTwinScan
