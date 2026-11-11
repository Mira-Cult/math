import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S015C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 31981613 widths0 = 165 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 31981613 32014381).card = 165 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 31981613 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 32014381 widths1 = 136 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 32014381 32047149).card = 136 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 32014381 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 32047149 widths2 = 142 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 32047149 32079917).card = 142 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 32047149 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 32079917 widths3 = 164 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 32079917 32112685).card = 164 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 32079917 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 31981613 32047149).card = 301 := by
  simpa using combineTwinPrimeSegments (by decide : 31981613 ≤ 32014381)
    (by decide : 32014381 ≤ 32047149) block0 block1

theorem join_0_1 : (twinPrimeSegment 32047149 32112685).card = 306 := by
  simpa using combineTwinPrimeSegments (by decide : 32047149 ≤ 32079917)
    (by decide : 32079917 ≤ 32112685) block2 block3

theorem join_1_0 : (twinPrimeSegment 31981613 32112685).card = 607 := by
  simpa using combineTwinPrimeSegments (by decide : 31981613 ≤ 32047149)
    (by decide : 32047149 ≤ 32112685) join_0_0 join_0_1

theorem total : (twinPrimeSegment 31981613 32112685).card = 607 := join_1_0

end S015C04
end Sude.GeneratedTwinScan
