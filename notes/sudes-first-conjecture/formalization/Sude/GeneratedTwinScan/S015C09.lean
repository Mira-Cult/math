import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S015C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 32636973 widths0 = 142 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 32636973 32669741).card = 142 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 32636973 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 32669741 widths1 = 147 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 32669741 32702509).card = 147 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 32669741 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 32702509 widths2 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 32702509 32735277).card = 110 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 32702509 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 32735277 widths3 = 151 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 32735277 32768045).card = 151 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 32735277 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 32636973 32702509).card = 289 := by
  simpa using combineTwinPrimeSegments (by decide : 32636973 ≤ 32669741)
    (by decide : 32669741 ≤ 32702509) block0 block1

theorem join_0_1 : (twinPrimeSegment 32702509 32768045).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 32702509 ≤ 32735277)
    (by decide : 32735277 ≤ 32768045) block2 block3

theorem join_1_0 : (twinPrimeSegment 32636973 32768045).card = 550 := by
  simpa using combineTwinPrimeSegments (by decide : 32636973 ≤ 32702509)
    (by decide : 32702509 ≤ 32768045) join_0_0 join_0_1

theorem total : (twinPrimeSegment 32636973 32768045).card = 550 := join_1_0

end S015C09
end Sude.GeneratedTwinScan
