import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S017C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 36438061 widths0 = 161 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 36438061 36470829).card = 161 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 36438061 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 36470829 widths1 = 153 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 36470829 36503597).card = 153 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 36470829 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 36503597 widths2 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 36503597 36536365).card = 127 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 36503597 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 36536365 widths3 = 139 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 36536365 36569133).card = 139 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 36536365 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 36438061 36503597).card = 314 := by
  simpa using combineTwinPrimeSegments (by decide : 36438061 ≤ 36470829)
    (by decide : 36470829 ≤ 36503597) block0 block1

theorem join_0_1 : (twinPrimeSegment 36503597 36569133).card = 266 := by
  simpa using combineTwinPrimeSegments (by decide : 36503597 ≤ 36536365)
    (by decide : 36536365 ≤ 36569133) block2 block3

theorem join_1_0 : (twinPrimeSegment 36438061 36569133).card = 580 := by
  simpa using combineTwinPrimeSegments (by decide : 36438061 ≤ 36503597)
    (by decide : 36503597 ≤ 36569133) join_0_0 join_0_1

theorem total : (twinPrimeSegment 36438061 36569133).card = 580 := join_1_0

end S017C06
end Sude.GeneratedTwinScan
