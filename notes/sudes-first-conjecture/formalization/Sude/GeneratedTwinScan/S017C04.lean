import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S017C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 36175917 widths0 = 141 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 36175917 36208685).card = 141 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 36175917 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 36208685 widths1 = 142 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 36208685 36241453).card = 142 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 36208685 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 36241453 widths2 = 144 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 36241453 36274221).card = 144 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 36241453 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 36274221 widths3 = 171 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 36274221 36306989).card = 171 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 36274221 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 36175917 36241453).card = 283 := by
  simpa using combineTwinPrimeSegments (by decide : 36175917 ≤ 36208685)
    (by decide : 36208685 ≤ 36241453) block0 block1

theorem join_0_1 : (twinPrimeSegment 36241453 36306989).card = 315 := by
  simpa using combineTwinPrimeSegments (by decide : 36241453 ≤ 36274221)
    (by decide : 36274221 ≤ 36306989) block2 block3

theorem join_1_0 : (twinPrimeSegment 36175917 36306989).card = 598 := by
  simpa using combineTwinPrimeSegments (by decide : 36175917 ≤ 36241453)
    (by decide : 36241453 ≤ 36306989) join_0_0 join_0_1

theorem total : (twinPrimeSegment 36175917 36306989).card = 598 := join_1_0

end S017C04
end Sude.GeneratedTwinScan
