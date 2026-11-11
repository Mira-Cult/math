import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S017C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 36569133 widths0 = 148 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 36569133 36601901).card = 148 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 36569133 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 36601901 widths1 = 165 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 36601901 36634669).card = 165 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 36601901 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 36634669 widths2 = 146 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 36634669 36667437).card = 146 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 36634669 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 36667437 widths3 = 143 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 36667437 36700205).card = 143 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 36667437 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 36569133 36634669).card = 313 := by
  simpa using combineTwinPrimeSegments (by decide : 36569133 ≤ 36601901)
    (by decide : 36601901 ≤ 36634669) block0 block1

theorem join_0_1 : (twinPrimeSegment 36634669 36700205).card = 289 := by
  simpa using combineTwinPrimeSegments (by decide : 36634669 ≤ 36667437)
    (by decide : 36667437 ≤ 36700205) block2 block3

theorem join_1_0 : (twinPrimeSegment 36569133 36700205).card = 602 := by
  simpa using combineTwinPrimeSegments (by decide : 36569133 ≤ 36634669)
    (by decide : 36634669 ≤ 36700205) join_0_0 join_0_1

theorem total : (twinPrimeSegment 36569133 36700205).card = 602 := join_1_0

end S017C07
end Sude.GeneratedTwinScan
