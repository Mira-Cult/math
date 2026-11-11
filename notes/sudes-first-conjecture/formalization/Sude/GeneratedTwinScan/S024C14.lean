import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinGeometricScan

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S024C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def widths0 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked0 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 52166701 widths0 = 144 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 52166701 52199469).card = 144 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 52166701 widths0
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked0] at h
  simpa [widths0] using h.symm

def widths1 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked1 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 52199469 widths1 = 140 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 52199469 52232237).card = 140 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 52199469 widths1
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked1] at h
  simpa [widths1] using h.symm

def widths2 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked2 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 52232237 widths2 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 52232237 52265005).card = 127 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 52232237 widths2
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked2] at h
  simpa [widths2] using h.symm

def widths3 : List ℕ := [4096, 4096, 4096, 4096]

theorem checked3 : geometricActiveStreamingTwinScan finiteTwinCheckedBase 52265005 widths3 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 52265005 52297773).card = 126 := by
  have h := geometricActiveStreamingTwinScan_spec finiteTwinCheckedBase 32768 52265005 widths3
    finiteTwinCheckedBase_complete (by decide) (by decide) (by decide)
  rw [checked3] at h
  simpa [widths3] using h.symm

theorem join_0_0 : (twinPrimeSegment 52166701 52232237).card = 284 := by
  simpa using combineTwinPrimeSegments (by decide : 52166701 ≤ 52199469)
    (by decide : 52199469 ≤ 52232237) block0 block1

theorem join_0_1 : (twinPrimeSegment 52232237 52297773).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 52232237 ≤ 52265005)
    (by decide : 52265005 ≤ 52297773) block2 block3

theorem join_1_0 : (twinPrimeSegment 52166701 52297773).card = 537 := by
  simpa using combineTwinPrimeSegments (by decide : 52166701 ≤ 52232237)
    (by decide : 52232237 ≤ 52297773) join_0_0 join_0_1

theorem total : (twinPrimeSegment 52166701 52297773).card = 537 := join_1_0

end S024C14
end Sude.GeneratedTwinScan
