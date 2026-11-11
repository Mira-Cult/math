import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S021C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 44695597 widths0 = 136 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 44695597 44728365).card = 136 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 44695597 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 44728365 widths1 = 150 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 44728365 44761133).card = 150 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 44728365 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 44761133 widths2 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 44761133 44793901).card = 133 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 44761133 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 44793901 widths3 = 143 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 44793901 44826669).card = 143 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 44793901 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 44695597 44761133).card = 286 := by
  simpa using combineTwinPrimeSegments (by decide : 44695597 ≤ 44728365)
    (by decide : 44728365 ≤ 44761133) block0 block1

theorem join_0_1 : (twinPrimeSegment 44761133 44826669).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 44761133 ≤ 44793901)
    (by decide : 44793901 ≤ 44826669) block2 block3

theorem join_1_0 : (twinPrimeSegment 44695597 44826669).card = 562 := by
  simpa using combineTwinPrimeSegments (by decide : 44695597 ≤ 44761133)
    (by decide : 44761133 ≤ 44826669) join_0_0 join_0_1

theorem total : (twinPrimeSegment 44695597 44826669).card = 562 := join_1_0

end S021C05
end Sude.GeneratedTwinScan
