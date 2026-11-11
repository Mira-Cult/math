import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S018C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 37748781 widths0 = 147 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 37748781 37781549).card = 147 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 37748781 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 37781549 widths1 = 138 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 37781549 37814317).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 37781549 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 37814317 widths2 = 138 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 37814317 37847085).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 37814317 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 37847085 widths3 = 145 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 37847085 37879853).card = 145 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 37847085 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 37748781 37814317).card = 285 := by
  simpa using combineTwinPrimeSegments (by decide : 37748781 ≤ 37781549)
    (by decide : 37781549 ≤ 37814317) block0 block1

theorem join_0_1 : (twinPrimeSegment 37814317 37879853).card = 283 := by
  simpa using combineTwinPrimeSegments (by decide : 37814317 ≤ 37847085)
    (by decide : 37847085 ≤ 37879853) block2 block3

theorem join_1_0 : (twinPrimeSegment 37748781 37879853).card = 568 := by
  simpa using combineTwinPrimeSegments (by decide : 37748781 ≤ 37814317)
    (by decide : 37814317 ≤ 37879853) join_0_0 join_0_1

theorem total : (twinPrimeSegment 37748781 37879853).card = 568 := join_1_0

end S018C00
end Sude.GeneratedTwinScan
