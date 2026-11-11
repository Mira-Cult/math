import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S018C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 38010925 widths0 = 152 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 38010925 38043693).card = 152 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 38010925 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 38043693 widths1 = 157 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 38043693 38076461).card = 157 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 38043693 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 38076461 widths2 = 142 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 38076461 38109229).card = 142 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 38076461 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 38109229 widths3 = 149 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 38109229 38141997).card = 149 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 38109229 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 38010925 38076461).card = 309 := by
  simpa using combineTwinPrimeSegments (by decide : 38010925 ≤ 38043693)
    (by decide : 38043693 ≤ 38076461) block0 block1

theorem join_0_1 : (twinPrimeSegment 38076461 38141997).card = 291 := by
  simpa using combineTwinPrimeSegments (by decide : 38076461 ≤ 38109229)
    (by decide : 38109229 ≤ 38141997) block2 block3

theorem join_1_0 : (twinPrimeSegment 38010925 38141997).card = 600 := by
  simpa using combineTwinPrimeSegments (by decide : 38010925 ≤ 38076461)
    (by decide : 38076461 ≤ 38141997) join_0_0 join_0_1

theorem total : (twinPrimeSegment 38010925 38141997).card = 600 := join_1_0

end S018C02
end Sude.GeneratedTwinScan
