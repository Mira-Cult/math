import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S019C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 41287725 widths0 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 41287725 41320493).card = 127 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 41287725 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 41320493 widths1 = 158 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 41320493 41353261).card = 158 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 41320493 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 41353261 widths2 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 41353261 41386029).card = 126 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 41353261 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 41386029 widths3 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 41386029 41418797).card = 122 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 41386029 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 41287725 41353261).card = 285 := by
  simpa using combineTwinPrimeSegments (by decide : 41287725 ≤ 41320493)
    (by decide : 41320493 ≤ 41353261) block0 block1

theorem join_0_1 : (twinPrimeSegment 41353261 41418797).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 41353261 ≤ 41386029)
    (by decide : 41386029 ≤ 41418797) block2 block3

theorem join_1_0 : (twinPrimeSegment 41287725 41418797).card = 533 := by
  simpa using combineTwinPrimeSegments (by decide : 41287725 ≤ 41353261)
    (by decide : 41353261 ≤ 41418797) join_0_0 join_0_1

theorem total : (twinPrimeSegment 41287725 41418797).card = 533 := join_1_0

end S019C11
end Sude.GeneratedTwinScan
