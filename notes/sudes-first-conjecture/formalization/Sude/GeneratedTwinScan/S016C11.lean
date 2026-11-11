import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S016C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 34996269 widths0 = 147 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 34996269 35029037).card = 147 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 34996269 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 35029037 widths1 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 35029037 35061805).card = 116 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 35029037 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 35061805 widths2 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 35061805 35094573).card = 122 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 35061805 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 35094573 widths3 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 35094573 35127341).card = 128 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 35094573 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 34996269 35061805).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 34996269 ≤ 35029037)
    (by decide : 35029037 ≤ 35061805) block0 block1

theorem join_0_1 : (twinPrimeSegment 35061805 35127341).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 35061805 ≤ 35094573)
    (by decide : 35094573 ≤ 35127341) block2 block3

theorem join_1_0 : (twinPrimeSegment 34996269 35127341).card = 513 := by
  simpa using combineTwinPrimeSegments (by decide : 34996269 ≤ 35061805)
    (by decide : 35061805 ≤ 35127341) join_0_0 join_0_1

theorem total : (twinPrimeSegment 34996269 35127341).card = 513 := join_1_0

end S016C11
end Sude.GeneratedTwinScan
