import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S021C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 44433453 widths0 = 146 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 44433453 44466221).card = 146 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 44433453 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 44466221 widths1 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 44466221 44498989).card = 127 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 44466221 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 44498989 widths2 = 141 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 44498989 44531757).card = 141 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 44498989 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 44531757 widths3 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 44531757 44564525).card = 129 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 44531757 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 44433453 44498989).card = 273 := by
  simpa using combineTwinPrimeSegments (by decide : 44433453 ≤ 44466221)
    (by decide : 44466221 ≤ 44498989) block0 block1

theorem join_0_1 : (twinPrimeSegment 44498989 44564525).card = 270 := by
  simpa using combineTwinPrimeSegments (by decide : 44498989 ≤ 44531757)
    (by decide : 44531757 ≤ 44564525) block2 block3

theorem join_1_0 : (twinPrimeSegment 44433453 44564525).card = 543 := by
  simpa using combineTwinPrimeSegments (by decide : 44433453 ≤ 44498989)
    (by decide : 44498989 ≤ 44564525) join_0_0 join_0_1

theorem total : (twinPrimeSegment 44433453 44564525).card = 543 := join_1_0

end S021C03
end Sude.GeneratedTwinScan
