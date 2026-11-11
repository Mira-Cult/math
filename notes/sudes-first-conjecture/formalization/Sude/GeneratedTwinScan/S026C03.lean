import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S026C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 54919213 widths0 = 145 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 54919213 54951981).card = 145 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 54919213 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 54951981 widths1 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 54951981 54984749).card = 125 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 54951981 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 54984749 widths2 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 54984749 55017517).card = 126 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 54984749 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 55017517 widths3 = 145 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 55017517 55050285).card = 145 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 55017517 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 54919213 54984749).card = 270 := by
  simpa using combineTwinPrimeSegments (by decide : 54919213 ≤ 54951981)
    (by decide : 54951981 ≤ 54984749) block0 block1

theorem join_0_1 : (twinPrimeSegment 54984749 55050285).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 54984749 ≤ 55017517)
    (by decide : 55017517 ≤ 55050285) block2 block3

theorem join_1_0 : (twinPrimeSegment 54919213 55050285).card = 541 := by
  simpa using combineTwinPrimeSegments (by decide : 54919213 ≤ 54984749)
    (by decide : 54984749 ≤ 55050285) join_0_0 join_0_1

theorem total : (twinPrimeSegment 54919213 55050285).card = 541 := join_1_0

end S026C03
end Sude.GeneratedTwinScan
