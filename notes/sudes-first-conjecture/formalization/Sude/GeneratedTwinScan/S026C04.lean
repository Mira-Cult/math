import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S026C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 55050285 widths0 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 55050285 55083053).card = 125 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 55050285 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 55083053 widths1 = 144 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 55083053 55115821).card = 144 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 55083053 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 55115821 widths2 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 55115821 55148589).card = 111 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 55115821 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 55148589 widths3 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 55148589 55181357).card = 134 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 55148589 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 55050285 55115821).card = 269 := by
  simpa using combineTwinPrimeSegments (by decide : 55050285 ≤ 55083053)
    (by decide : 55083053 ≤ 55115821) block0 block1

theorem join_0_1 : (twinPrimeSegment 55115821 55181357).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 55115821 ≤ 55148589)
    (by decide : 55148589 ≤ 55181357) block2 block3

theorem join_1_0 : (twinPrimeSegment 55050285 55181357).card = 514 := by
  simpa using combineTwinPrimeSegments (by decide : 55050285 ≤ 55115821)
    (by decide : 55115821 ≤ 55181357) join_0_0 join_0_1

theorem total : (twinPrimeSegment 55050285 55181357).card = 514 := join_1_0

end S026C04
end Sude.GeneratedTwinScan
