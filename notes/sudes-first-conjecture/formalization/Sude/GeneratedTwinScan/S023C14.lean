import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S023C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 50069549 widths0 = 137 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 50069549 50102317).card = 137 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 50069549 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 50102317 widths1 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 50102317 50135085).card = 127 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 50102317 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 50135085 widths2 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 50135085 50167853).card = 125 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 50135085 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 50167853 widths3 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 50167853 50200621).card = 131 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 50167853 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 50069549 50135085).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 50069549 ≤ 50102317)
    (by decide : 50102317 ≤ 50135085) block0 block1

theorem join_0_1 : (twinPrimeSegment 50135085 50200621).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 50135085 ≤ 50167853)
    (by decide : 50167853 ≤ 50200621) block2 block3

theorem join_1_0 : (twinPrimeSegment 50069549 50200621).card = 520 := by
  simpa using combineTwinPrimeSegments (by decide : 50069549 ≤ 50135085)
    (by decide : 50135085 ≤ 50200621) join_0_0 join_0_1

theorem total : (twinPrimeSegment 50069549 50200621).card = 520 := join_1_0

end S023C14
end Sude.GeneratedTwinScan
