import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S018C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 39452717 widths0 = 152 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 39452717 39485485).card = 152 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 39452717 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 39485485 widths1 = 154 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 39485485 39518253).card = 154 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 39485485 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 39518253 widths2 = 143 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 39518253 39551021).card = 143 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 39518253 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 39551021 widths3 = 140 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 39551021 39583789).card = 140 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 39551021 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 39452717 39518253).card = 306 := by
  simpa using combineTwinPrimeSegments (by decide : 39452717 ≤ 39485485)
    (by decide : 39485485 ≤ 39518253) block0 block1

theorem join_0_1 : (twinPrimeSegment 39518253 39583789).card = 283 := by
  simpa using combineTwinPrimeSegments (by decide : 39518253 ≤ 39551021)
    (by decide : 39551021 ≤ 39583789) block2 block3

theorem join_1_0 : (twinPrimeSegment 39452717 39583789).card = 589 := by
  simpa using combineTwinPrimeSegments (by decide : 39452717 ≤ 39518253)
    (by decide : 39518253 ≤ 39583789) join_0_0 join_0_1

theorem total : (twinPrimeSegment 39452717 39583789).card = 589 := join_1_0

end S018C13
end Sude.GeneratedTwinScan
