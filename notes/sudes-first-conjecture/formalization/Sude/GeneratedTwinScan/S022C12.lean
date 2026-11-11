import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S022C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 47710253 widths0 = 143 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 47710253 47743021).card = 143 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 47710253 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 47743021 widths1 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 47743021 47775789).card = 121 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 47743021 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 47775789 widths2 = 144 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 47775789 47808557).card = 144 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 47775789 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 47808557 widths3 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 47808557 47841325).card = 127 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 47808557 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 47710253 47775789).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 47710253 ≤ 47743021)
    (by decide : 47743021 ≤ 47775789) block0 block1

theorem join_0_1 : (twinPrimeSegment 47775789 47841325).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 47775789 ≤ 47808557)
    (by decide : 47808557 ≤ 47841325) block2 block3

theorem join_1_0 : (twinPrimeSegment 47710253 47841325).card = 535 := by
  simpa using combineTwinPrimeSegments (by decide : 47710253 ≤ 47775789)
    (by decide : 47775789 ≤ 47841325) join_0_0 join_0_1

theorem total : (twinPrimeSegment 47710253 47841325).card = 535 := join_1_0

end S022C12
end Sude.GeneratedTwinScan
