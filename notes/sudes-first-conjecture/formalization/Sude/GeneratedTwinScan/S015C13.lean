import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S015C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 33161261 widths0 = 153 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 33161261 33194029).card = 153 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 33161261 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 33194029 widths1 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 33194029 33226797).card = 133 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 33194029 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 33226797 widths2 = 166 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 33226797 33259565).card = 166 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 33226797 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 33259565 widths3 = 144 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 33259565 33292333).card = 144 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 33259565 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 33161261 33226797).card = 286 := by
  simpa using combineTwinPrimeSegments (by decide : 33161261 ≤ 33194029)
    (by decide : 33194029 ≤ 33226797) block0 block1

theorem join_0_1 : (twinPrimeSegment 33226797 33292333).card = 310 := by
  simpa using combineTwinPrimeSegments (by decide : 33226797 ≤ 33259565)
    (by decide : 33259565 ≤ 33292333) block2 block3

theorem join_1_0 : (twinPrimeSegment 33161261 33292333).card = 596 := by
  simpa using combineTwinPrimeSegments (by decide : 33161261 ≤ 33226797)
    (by decide : 33226797 ≤ 33292333) join_0_0 join_0_1

theorem total : (twinPrimeSegment 33161261 33292333).card = 596 := join_1_0

end S015C13
end Sude.GeneratedTwinScan
