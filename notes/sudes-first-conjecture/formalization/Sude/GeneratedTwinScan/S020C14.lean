import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S020C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 43778093 widths0 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 43778093 43810861).card = 127 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 43778093 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 43810861 widths1 = 136 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 43810861 43843629).card = 136 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 43810861 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 43843629 widths2 = 131 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 43843629 43876397).card = 131 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 43843629 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 43876397 widths3 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 43876397 43909165).card = 135 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 43876397 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 43778093 43843629).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 43778093 ≤ 43810861)
    (by decide : 43810861 ≤ 43843629) block0 block1

theorem join_0_1 : (twinPrimeSegment 43843629 43909165).card = 266 := by
  simpa using combineTwinPrimeSegments (by decide : 43843629 ≤ 43876397)
    (by decide : 43876397 ≤ 43909165) block2 block3

theorem join_1_0 : (twinPrimeSegment 43778093 43909165).card = 529 := by
  simpa using combineTwinPrimeSegments (by decide : 43778093 ≤ 43843629)
    (by decide : 43843629 ≤ 43909165) join_0_0 join_0_1

theorem total : (twinPrimeSegment 43778093 43909165).card = 529 := join_1_0

end S020C14
end Sude.GeneratedTwinScan
