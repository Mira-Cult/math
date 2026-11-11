import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S015C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 31719469 widths0 = 143 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 31719469 31752237).card = 143 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 31719469 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 31752237 widths1 = 145 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 31752237 31785005).card = 145 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 31752237 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 31785005 widths2 = 138 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 31785005 31817773).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 31785005 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 31817773 widths3 = 145 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 31817773 31850541).card = 145 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 31817773 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 31719469 31785005).card = 288 := by
  simpa using combineTwinPrimeSegments (by decide : 31719469 ≤ 31752237)
    (by decide : 31752237 ≤ 31785005) block0 block1

theorem join_0_1 : (twinPrimeSegment 31785005 31850541).card = 283 := by
  simpa using combineTwinPrimeSegments (by decide : 31785005 ≤ 31817773)
    (by decide : 31817773 ≤ 31850541) block2 block3

theorem join_1_0 : (twinPrimeSegment 31719469 31850541).card = 571 := by
  simpa using combineTwinPrimeSegments (by decide : 31719469 ≤ 31785005)
    (by decide : 31785005 ≤ 31850541) join_0_0 join_0_1

theorem total : (twinPrimeSegment 31719469 31850541).card = 571 := join_1_0

end S015C02
end Sude.GeneratedTwinScan
