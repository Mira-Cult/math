import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S027C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 58458157 widths0 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 58458157 58490925).card = 129 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 58458157 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 58490925 widths1 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 58490925 58523693).card = 127 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 58490925 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 58523693 widths2 = 138 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 58523693 58556461).card = 138 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 58523693 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 58556461 widths3 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 58556461 58589229).card = 119 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 58556461 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 58458157 58523693).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 58458157 ≤ 58490925)
    (by decide : 58490925 ≤ 58523693) block0 block1

theorem join_0_1 : (twinPrimeSegment 58523693 58589229).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 58523693 ≤ 58556461)
    (by decide : 58556461 ≤ 58589229) block2 block3

theorem join_1_0 : (twinPrimeSegment 58458157 58589229).card = 513 := by
  simpa using combineTwinPrimeSegments (by decide : 58458157 ≤ 58523693)
    (by decide : 58523693 ≤ 58589229) join_0_0 join_0_1

theorem total : (twinPrimeSegment 58458157 58589229).card = 513 := join_1_0

end S027C14
end Sude.GeneratedTwinScan
