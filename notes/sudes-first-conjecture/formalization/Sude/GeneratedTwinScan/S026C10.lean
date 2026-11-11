import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S026C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 55836717 widths0 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 55836717 55869485).card = 131 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 55836717 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 55869485 widths1 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 55869485 55902253).card = 130 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 55869485 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 55902253 widths2 = 134 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 55902253 55935021).card = 134 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 55902253 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 55935021 widths3 = 144 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 55935021 55967789).card = 144 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 55935021 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 55836717 55902253).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 55836717 ≤ 55869485)
    (by decide : 55869485 ≤ 55902253) block0 block1

theorem join_0_1 : (twinPrimeSegment 55902253 55967789).card = 278 := by
  simpa using combineTwinPrimeSegments (by decide : 55902253 ≤ 55935021)
    (by decide : 55935021 ≤ 55967789) block2 block3

theorem join_1_0 : (twinPrimeSegment 55836717 55967789).card = 539 := by
  simpa using combineTwinPrimeSegments (by decide : 55836717 ≤ 55902253)
    (by decide : 55902253 ≤ 55967789) join_0_0 join_0_1

theorem total : (twinPrimeSegment 55836717 55967789).card = 539 := join_1_0

end S026C10
end Sude.GeneratedTwinScan
