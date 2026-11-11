import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S024C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 51118125 widths0 = 143 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 51118125 51150893).card = 143 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 51118125 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 51150893 widths1 = 142 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 51150893 51183661).card = 142 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 51150893 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 51183661 widths2 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 51183661 51216429).card = 126 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 51183661 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 51216429 widths3 = 155 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 51216429 51249197).card = 155 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 51216429 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 51118125 51183661).card = 285 := by
  simpa using combineTwinPrimeSegments (by decide : 51118125 ≤ 51150893)
    (by decide : 51150893 ≤ 51183661) block0 block1

theorem join_0_1 : (twinPrimeSegment 51183661 51249197).card = 281 := by
  simpa using combineTwinPrimeSegments (by decide : 51183661 ≤ 51216429)
    (by decide : 51216429 ≤ 51249197) block2 block3

theorem join_1_0 : (twinPrimeSegment 51118125 51249197).card = 566 := by
  simpa using combineTwinPrimeSegments (by decide : 51118125 ≤ 51183661)
    (by decide : 51183661 ≤ 51249197) join_0_0 join_0_1

theorem total : (twinPrimeSegment 51118125 51249197).card = 566 := join_1_0

end S024C06
end Sude.GeneratedTwinScan
